from z3 import *

# track variable names that should be treated as arrays
_array_vars = set()
# _array_lengths: name -> z3.Int('len_<name>') canonical symbol (created on-demand) OR an int for concrete lengths
_array_lengths = {}
# procedures: name -> dict with keys: params, requires, ensures, body
_procedures = {}
# record procedures that failed verification; if non-empty, the whole program
# should not be reported as correct even if the global VC holds
_failed_procedures = []

def _replace_old_nodes(node, func_name):
    """Replace ['old', ['var', p]] with ['var', '__old_<p>_<func>'] in the AST node (recursively).
    Only supports old(var) currently.
    """
    if not isinstance(node, list):
        return node
    if len(node) == 0:
        return node
    head = node[0]
    if head == 'old':
        # expect ['old', ['var', name]]
        arg = node[1]
        if isinstance(arg, list) and arg[0] == 'var':
            name = arg[1]
            return ['var', f"__old_{name}_{func_name}"]
        else:
            raise NotImplementedError("old(...) currently only supports variables")
    # otherwise recurse
    return [head] + [_replace_old_nodes(child, func_name) for child in node[1:]]

def _replace_vars_mapping(node, mapping):
    """Replace occurrences of ['var', name] according to mapping dict {name: newname}.
    Works recursively on the AST lists.
    """
    if not isinstance(node, list):
        return node
    if len(node) == 0:
        return node
    if node[0] == 'var':
        name = node[1]
        return ['var', mapping.get(name, name)]
    return [node[0]] + [_replace_vars_mapping(child, mapping) for child in node[1:]]

def _ensure_len_symbol(name):
    """Return the canonical z3.Int symbol for length of `name` (create if needed)."""
    if name in _array_lengths and not isinstance(_array_lengths[name], int):
        return _array_lengths[name]
    sym = Int(f"len_{name}")
    _array_lengths[name] = sym
    return sym

def wp(stmt, post):
    match stmt:
        case ['seq', *rest]:
            for s in reversed(rest):
                post = wp(s, post)
            return post

        case ['assume', cond]:
            cond_z3 = expr_to_z3(cond)
            return Implies(cond_z3, post)

        case ['assert', cond]:
            cond_z3 = expr_to_z3(cond)
            return And(cond_z3, post)

        case ['if', test, body, orelse]:
            test_z3 = expr_to_z3(test)
            wp_body = wp(['seq'] + body, post)
            wp_orelse = wp(['seq'] + orelse, post)
            return And(Implies(test_z3, wp_body), Implies(Not(test_z3), wp_orelse))

        case ['skip']:
            return post

        case ['requires', cond]:
            # treat requires in a body as metadata (handled separately); skip
            return post

        case ['ensures', cond]:
            # treat ensures in a body as metadata (handled separately); skip
            return post

        case ['assign', var, expr]:
            expr_z3 = expr_to_z3(expr)

            is_array_assign = False
            if isinstance(expr, list) and expr and expr[0] == 'array':
                is_array_assign = True
            if isinstance(expr, list) and expr and expr[0] == 'var' and expr[1] in _array_vars:
                is_array_assign = True
            if isinstance(expr, list) and expr and expr[0] == 'arrvar':
                is_array_assign = True

            # record length info for array assignments
            if is_array_assign:
                # mark var as an array name
                _array_vars.add(var)

                # RHS is a literal array -> concrete length known
                if isinstance(expr, list) and expr and expr[0] == 'array':
                    elems = expr[1:]
                    concrete_len = len(elems)

                    # If earlier we created a symbolic length for this var (e.g., when processing
                    # asserts before the assign), substitute that symbolic length with the concrete int in post.
                    old_len = _array_lengths.get(var)
                    if old_len is not None and not isinstance(old_len, int):
                        post = substitute(post, (old_len, IntVal(concrete_len)))

                    # store concrete length (as int)
                    _array_lengths[var] = concrete_len

                    # substitute the array variable with the RHS Z3 array term
                    return substitute(post, (Array(var, IntSort(), IntSort()), expr_z3))

                # RHS is a named array variable (alias): copy whatever length info exists (int or symbol)
                elif isinstance(expr, list) and expr and expr[0] in ('var', 'arrvar'):
                    src_name = expr[1]
                    if src_name in _array_lengths:
                        _array_lengths[var] = _array_lengths[src_name]
                    # ensure source is treated as array
                    _array_vars.add(src_name)
                    return substitute(post, (Array(var, IntSort(), IntSort()), expr_z3))

                # other array expression (e.g., expression that is already an array term): just substitute
                else:
                    # ensure there's a canonical symbol for var (symbolic) if needed
                    _array_lengths.setdefault(var, _ensure_len_symbol(var))
                    return substitute(post, (Array(var, IntSort(), IntSort()), expr_z3))

            else:
                # scalar assignment: remove any prior array metadata for this var
                if var in _array_vars:
                    _array_vars.discard(var)
                    _array_lengths.pop(var, None)
                return substitute(post, (Int(var), expr_z3))

        case ['return', *rest]:
            # On return, bind the special symbol `ret` to the returned expression
            # in the postcondition so `ensures` can refer to the return value.
            if len(rest) == 0:
                # no return value -> use 0 as a sentinel
                return substitute(post, (Int('ret'), IntVal(0)))
            ret_expr = rest[0]
            ret_z3 = expr_to_z3(ret_expr)
            return substitute(post, (Int('ret'), ret_z3))

        case ['tastore', arr, idx, val]:
            arr_z3 = expr_to_z3(arr)
            idx_z3 = expr_to_z3(idx)
            val_z3 = expr_to_z3(val)
            if isinstance(arr, list) and arr and arr[0] == 'arrvar':
                _array_vars.add(arr[1])
            new_arr = Store(arr_z3, idx_z3, val_z3)
            return substitute(post, (arr_z3, new_arr))

        case ['invariant', *rest]:
            # invariants do not affect the weakest precondition
            return BoolVal(True)
        
        case ['proc', name, params, requires, ensures, body]:
            # register procedure contracts for later use
            _procedures[name] = {
                'params': params,
                'requires': requires,
                'ensures': ensures,
                'body': body,
            }

            # Verify the procedure: under requires (on initial param values), the
            # body should establish ensures. We model initial parameter values
            # as special variables named __old_<p>_<proc> and replace old(p)
            # occurrences in ensures with those symbols.
            # 1) build requires_z3 over initial values
            req_conjs = []
            for r in requires:
                req_conjs.append(expr_to_z3(r))
            requires_z3 = And(*req_conjs) if req_conjs else BoolVal(True)

            # 2) build ensures_z3 where old(p) -> __old_p_func
            ens_conjs = []
            for e in ensures:
                e2 = _replace_old_nodes(e, name)
                ens_conjs.append(expr_to_z3(e2))
            ensures_z3 = And(*ens_conjs) if ens_conjs else BoolVal(True)

            # 3) compute WP of the procedure body w.r.t. ensures
            pre_for_body = wp(['seq'] + body, ensures_z3)

            # 4) check that requires => pre_for_body is valid
            solver = Solver()
            # parameters at function entry equal the __old_<p>_<func> symbols
            entry_eqs = [Int(p) == Int(f"__old_{p}_{name}") for p in params]
            solver.add(requires_z3)
            solver.add(*entry_eqs)
            solver.add(Not(pre_for_body))
            ok = solver.check() == unsat
            if not ok:
                print(f"Procedure {name} FAILED verification; counterexample:")
                print(solver.model())
                _failed_procedures.append(name)
            else:
                print(f"Procedure {name} verified.")

            # procedure definitions do not change the WP of the surrounding code
            return post

        case ['while', cond, body, invariants]:
            cond_z3 = expr_to_z3(cond)
            invariant = And(*list(map(expr_to_z3, invariants))) if invariants else BoolVal(True)
            wp_body = wp(['seq'] + body, invariant)
            return And(invariant, Implies(And(invariant, cond_z3), wp_body), Implies(And(invariant, Not(cond_z3)), post))

        case _:
            raise NotImplementedError(stmt)

def expr_to_z3(expr):
    match expr:
        case ['const', v]:
            if isinstance(v, bool):
                return BoolVal(v)
            else:
                return IntVal(v)

        case ['var', name]:
            if name in _array_vars:
                return Array(name, IntSort(), IntSort())
            return Int(name)

        case ['arrvar', name]:
            _array_vars.add(name)
            return Array(name, IntSort(), IntSort())

        case ['array', *elems]:
            arr = K(IntSort(), IntVal(0))
            for i, e in enumerate(elems):
                arr = Store(arr, IntVal(i), expr_to_z3(e))
            return arr

        case ['select', arr, idx]:
            return Select(expr_to_z3(arr), expr_to_z3(idx))

        case ['len', arr]:
            # inline array literal: return concrete int
            if isinstance(arr, list) and arr and arr[0] == 'array':
                # arr[1:] are elements
                return IntVal(len(arr) - 1)

            # named array variable (arrvar or var): return concrete int if known, else canonical symbol
            if isinstance(arr, list) and arr and arr[0] in ('arrvar', 'var'):
                name = arr[1]
                if name in _array_lengths:
                    length_info = _array_lengths[name]
                    return IntVal(length_info) if isinstance(length_info, int) else length_info
                # create a symbolic length Int for this named array
                sym_len = Int(f"len_{name}")
                _array_lengths[name] = sym_len
                return sym_len

            # fallback for complex expressions: create a fresh anonymous length symbol
            if not hasattr(expr_to_z3, "_len_counter"):
                expr_to_z3._len_counter = 0
            expr_to_z3._len_counter += 1
            return Int(f"len_unknown_{expr_to_z3._len_counter}")

        case ['<', a, b]:
            return expr_to_z3(a) < expr_to_z3(b)
        case ['<=', a, b]:
            return expr_to_z3(a) <= expr_to_z3(b)
        case ['>', a, b]:
            return expr_to_z3(a) > expr_to_z3(b)
        case ['>=', a, b]:
            return expr_to_z3(a) >= expr_to_z3(b)
        case ['==', a, b]:
            return expr_to_z3(a) == expr_to_z3(b)
        case ['!=', a, b]:
            return expr_to_z3(a) != expr_to_z3(b)

        case ['+', a, b]:
            return expr_to_z3(a) + expr_to_z3(b)

        case ['-', x] :
            # unary negation
            return -expr_to_z3(x)
        case ['-', a, b]:
            return expr_to_z3(a) - expr_to_z3(b)

        case ['*', a, b]:
            return expr_to_z3(a) * expr_to_z3(b)
        case ['/', a, b]:
            return expr_to_z3(a) / expr_to_z3(b)

        case ['and', *args]:
            # logical conjunction of multiple boolean sub-expressions
            return And(*[expr_to_z3(a) for a in args])

        case _:
            raise NotImplementedError(expr)


def prove(stmt):
    post = BoolVal(True)
    pre = wp(stmt, post)
    print(pre)
    s = Solver()
    s.add(Not(pre))
    res = s.check()

    # If any procedure failed verification earlier, the whole program is
    # considered incorrect even if the global VC holds.
    if _failed_procedures:
        print("The following procedures FAILED verification:", _failed_procedures)
        print("The program is incorrect.")
        return

    if res == unsat:
        print("The program is correct.")
    else:
        print("The program is incorrect.")
        print(s.model())

if __name__ == "__main__":
    from parser import py_ast, WhilePyVisitor
    import sys
    filename = sys.argv[1]
    tree = py_ast(filename)
    visitor = WhilePyVisitor()
    stmt = visitor.visit(tree)
    print("Program AST:", stmt)
    prove(stmt)
