from z3 import *

# track variable names that should be treated as arrays
_array_vars = set()
# _array_lengths: name -> z3.Int('len_<name>') canonical symbol (created on-demand) OR an int for concrete lengths
_array_lengths = {}
_array_aliases = {}
# procedures: name -> dict with keys: params, requires, ensures, body
_procedures = {}
# record procedures that failed verification; if non-empty, the whole program
# should not be reported as correct even if the global VC holds
_failed_procedures = []

_ssa_versions = {}
_ssa_map = {}

def get_ssa(name):
    return _ssa_map.get(name, f"__ssa_{name}_0")

def fresh_ssa(name):
    ver = _ssa_versions.get(name, 0)
    ver = ver + 1
    _ssa_versions[name] = ver
    _ssa_map[name] = f"__ssa_{name}_{ver}"
    return _ssa_map[name]

def _resolve_array_name(name):
    seen = set()
    cur = name
    while cur in _array_aliases and cur not in seen:
        seen.add(cur)
        cur = _array_aliases[cur]
    return cur

def _normalize_post_arrays(post):
    """Rewrite any Array(var,...) occurrences in `post` to use the canonical name.
    Returns the rewritten post. Uses the current _array_aliases mapping.
    """
    # collect substitutions to do (avoid modifying _array_vars during iteration)
    subs = []
    for name in list(_array_vars):
        canon = _resolve_array_name(name)
        if canon != name:
            subs.append((Array(name, IntSort(), IntSort()), Array(canon, IntSort(), IntSort())))
    if not subs:
        return post
    # perform all substitutions at once
    return substitute(post, *subs)

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

def _find_vars_in_assurances(node):
    """Recursively find all variable names that occur as ['var', name] in the AST list."""
    vars_found = set()

    if not isinstance(node, list):
        return vars_found
    if len(node) == 0:
        return vars_found
    
    if node[0] == 'var' and len(node) > 1:
        vars_found.add(node[1])
        return vars_found
    
    for child in node[1:]:
        vars_found |= _find_vars_in_assurances(child)
    return vars_found

def _ensure_len_symbol(name):
    """Return the canonical z3.Int symbol for length of `name` (create if needed)."""
    if name in _array_lengths and not isinstance(_array_lengths[name], int):
        return _array_lengths[name]
    sym = Int(f"len_{name}")
    _array_lengths[name] = sym
    return sym

def find_modified_vars(stmt):
    """
    Return a set of variable names that are assigned or modified within stmt.
    Handles:
      - ['assign', var, expr]
      - ['call', proc, args] (uses the 'modifies' list of that proc)
      - ['if', cond, then, else]
      - ['while', cond, inv, body]
      - sequences (list of statements)
    """
    modified = set()

    if stmt is None:
        return modified

    # handle sequence of statements
    if isinstance(stmt, list) and stmt and isinstance(stmt[0], list):
        for s in stmt:
            modified |= find_modified_vars(s)
        return modified

    # single statement node
    match stmt:
        case ['seq', *rest]:
            for s in rest:
                modified |= find_modified_vars(s)
            return modified

        case ['assign', var, expr]:
            modified.add(var)
            modified |= find_modified_vars(expr)
            # also handle array element assignments (e.g., ['assign', ['arrstore', 'A', i], e])
            if isinstance(var, list) and var and var[0] == 'arrstore':
                modified.add(var[1])
            return modified

        case ['call', proc, args]:
            # use modifies clause of the procedure if available
            if proc in _procedures:
                modset = set(_procedures[proc].get('modifies', []))
                modified |= modset
            return modified

        case ['if', cond, then_branch, else_branch]:
            modified |= find_modified_vars(then_branch)
            modified |= find_modified_vars(else_branch)
            return modified

        case ['while', cond, invariant, body]:
            modified |= find_modified_vars(body)
            return modified

        case _:
            # other statement types (assert, assume, skip, etc.)
            return modified

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
        
        case ['modifies', cond]:
            return post

        case ['assign', var, expr]:
            if isinstance(expr, list) and expr and (expr[0] == 'call'):
                # return wp(expr, substitute(post, (Int(var), Int(f"__ret_{expr[1]}_{_call_counter+1}"))))
                old_var = get_ssa(var)
                fresh = fresh_ssa(var) # if var appears on rhs, this will fix issues
                print("proc call", old_var, fresh)
                # return wp(expr, substitute(post, (Int(old_var), Int(fresh_ssa("ret")))))
                return substitute(wp(expr, post), (Int(get_ssa("ret")), Int(old_var)))
                # cannot do the following way because this can lead to variable having multiple different values
                # return substitute(wp(expr, post), (Int(f"__ret_{expr[1]}_{_call_counter}"), Int(var)))
                # return substitute(wp(expr, post), (Int(var), Int(f"__ret_{expr[1]}_{_call_counter}")))

            expr_z3 = expr_to_z3(expr)

            is_array_assign = False
            if isinstance(expr, list) and expr and (expr[0] == 'array' or expr[0] == 'arrvar'):
                is_array_assign = True
            if isinstance(expr, list) and expr and expr[0] == 'var' and (expr[1] in _array_vars or var in _array_vars):
                # print("test")
                is_array_assign = True
            # print(expr)
            # if isinstance(expr, list) and expr and expr[0] == 'var':
            #     print(expr[1] in _array_vars)

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
                    _array_lengths[var] = concrete_len

                    # ????
                    _array_aliases.pop(var, None)
                    canon = _resolve_array_name(var)
                    post = _normalize_post_arrays(post)
                    return substitute(post, (Array(canon, IntSort(), IntSort()), expr_z3))

                # RHS is a named array variable (alias): copy whatever length info exists (int or symbol)
                elif isinstance(expr, list) and expr and expr[0] in ('var', 'arrvar'):
                    src_name = expr[1]
                    _array_vars.add(src_name)
                    if src_name in _array_lengths:
                        _array_lengths[var] = _array_lengths[src_name]
                    canon_src = _resolve_array_name(src_name)
                    _array_aliases[var] = canon_src
                    post = _normalize_post_arrays(post)
                    return substitute(post, (Array(var, IntSort(), IntSort()), Array(canon_src, IntSort(), IntSort())))
                
                # other array expression (e.g., expression that is already an array term): just substitute
                else:
                    # ensure there's a canonical symbol for var (symbolic) if needed
                    _array_lengths.setdefault(var, _ensure_len_symbol(var))
                    _array_aliases.pop(var, None)
                    canon = _resolve_array_name(var)
                    post = _normalize_post_arrays(post)
                    return substitute(post, (Array(canon, IntSort(), IntSort()), expr_z3))
                

            else:
                # scalar assignment: remove any prior array metadata for this var
                if var in _array_vars:
                    _array_vars.discard(var)
                    _array_lengths.pop(var, None)
                    _array_aliases.pop(var, None)

                old_var = get_ssa(var)
                fresh_var = fresh_ssa(var)
                print(old_var, fresh_var)

                # if the variable appeared on rhs, we want to substitute it for fresh names
                expr_z3 = substitute(expr_z3, (Int(old_var), Int(fresh_var)))

                return substitute(post, (Int(old_var), expr_z3))

        case ['return', *rest]:
            # On return, bind the special symbol `ret` to the returned expression
            # in the postcondition so `ensures` can refer to the return value.
            if len(rest) == 0:
                # no return value -> use 0 as a sentinel
                return substitute(post, (Int(get_ssa('ret')), IntVal(0)))
            ret_expr = rest[0]
            ret_z3 = expr_to_z3(ret_expr)
            return substitute(post, (Int(get_ssa('ret')), ret_z3))

        case ['store', arr, idx, val]:
            arr_z3 = expr_to_z3(arr)
            idx_z3 = expr_to_z3(idx)
            val_z3 = expr_to_z3(val)
            if isinstance(arr, list) and arr and arr[0] == 'arrvar':
                print("true")
                arr_name = arr[1]
                _array_vars.add(arr_name)
                canon = _resolve_array_name(arr_name)
                arr_z3 = Array(canon, IntSort(), IntSort())
            else:
                print("false")
                arr_z3 = expr_to_z3(arr)

            new_arr = Store(arr_z3, idx_z3, val_z3)
            print(arr_z3)
            print(new_arr)
            return substitute(post, (arr_z3, new_arr))

        case ['invariant', *rest]:
            # invariants do not affect the weakest precondition
            return post
        
        case ['proc', name, params, body, requires, ensures, modifies]:
            # register procedure contracts for later use
            _procedures[name] = {
                'params': params,
                'body': body,
                'requires': requires,
                'ensures': ensures,
                'modifies': modifies,
            }

            # Verify the procedure: under requires (on initial param values), the
            # body should establish ensures. We model initial parameter values
            # as special variables named __old_<p>_<proc> and replace old(p)
            # occurrences in ensures with those symbols.

            # 1) build ensures_z3 where old(p) -> __old_p_func
            ens_conjs = [expr_to_z3(e) for e in ensures]
            ensures_z3 = And(*ens_conjs) if ens_conjs else BoolVal(True)
            
            # 2) compute WP of the procedure body w.r.t. ensures
            pre_for_body = wp(['seq'] + body, ensures_z3)

            # 3) build requires_z3 over initial values
            req_conjs = [expr_to_z3(r) for r in requires]
            requires_z3 = And(*req_conjs) if req_conjs else BoolVal(True)
            # parameters at function entry equal the __old_<p>_<func> symbols
            entry_eqs = [Int(get_ssa(p)) == Int(f"__old_{p}") for p in params]

            # 4) check that requires => pre_for_body is valid
            solver = Solver()
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
            body = ["seq"] + body
            
            assurance_vars = set()
            for i in invariants:
                assurance_vars |= _find_vars_in_assurances(i)
            print("assurance vars", assurance_vars)

            old_vars = [Int(get_ssa(m)) for m in assurance_vars]
            wp_body = wp(body, invariant)
            # print("wp_body", wp_body)
            mod_vars = [Int(get_ssa(m)) for m in assurance_vars]
            
            
            print("invariant", invariant)
            print("old_vars", old_vars)
            print("mod_vars", mod_vars)
            old_new = [sub for sub in zip(old_vars, mod_vars)]
            new_old = [sub for sub in zip(mod_vars, old_vars)]
            
            for m in assurance_vars:
                fresh_ssa(m)

            # cond_true = substitute(Implies(And(invariant, cond_z3), wp_body), *old_new)
            new_invariant = substitute(invariant, *old_new)
            new_cond_z3 = substitute(cond_z3, *old_new)
            cond_true = Implies(And(new_invariant, new_cond_z3), wp_body)
            print("cond_true", cond_true)
            # cond_true = Implies(And(invariant, cond_z3), substitute(wp_body, *new_old))
            # cond_true = substitute(cond_true, *[sub for sub in zip(old_vars, mod_vars)])
            # print("cond_true", cond_true)
            # print("wp_body", wp_body)
            cond_false = Implies(And(invariant, Not(cond_z3)), post)
            preinvariant = And(*list(map(expr_to_z3, invariants))) if invariants else BoolVal(True)
            # print("preinvariant", preinvariant)
            return And(preinvariant, cond_true, cond_false)
            # return And(invariant, substitute(Implies(And(invariant, cond_z3), wp_body), *mod_sub), substitute(Implies(And(invariant, Not(cond_z3)), post), *mod_sub))
        
        case ['call', proc, args]:
            procedure = _procedures[proc]
            params = procedure['params']
            requires = procedure['requires']
            ensures = procedure['ensures']
            modifies = procedure['modifies']

            # substitute params for args in order
            param_ast_map = {p: a for p, a in zip(params, args)}
            
            # replace all parameters in requires with their arguments 
            param_substitutions = [(Int(get_ssa(p)), expr_to_z3(a)) for (p, a) in param_ast_map.items()]
            requires_inst_z3_list = [substitute(expr_to_z3(r), *param_substitutions) for r in requires]
            requires_inst = And(*requires_inst_z3_list) if requires_inst_z3_list else BoolVal(True)

            # give params fresh names
            fresh_ssa("ret")
            for p in params:
                fresh_ssa(p)
            
            ensures_inst_z3_list = [expr_to_z3(e) for e in ensures]
            ensures_inst = And(*ensures_inst_z3_list) if ensures_inst_z3_list else BoolVal(True)
            # unmodified variables should remain the same
            unmodified_vars = []
            for p, a in param_ast_map.items():
                if p not in modifies:
                    unmodified_vars.append(Int(f"__old_{p}") == expr_to_z3(a))
            ensures_inst = And(ensures_inst, *unmodified_vars) if unmodified_vars else ensures_inst
            # replace all old parameters in ensures with their arguments
            old_substitutions = [(Int(f"__old_{p}"), expr_to_z3(a)) for (p, a) in param_ast_map.items()]
            ensures_inst = substitute(ensures_inst, *old_substitutions)

            # any variable that gets modified needs to be substituted in the post condition
            modifies_substitution = []
            for var in modifies:
                sub = param_ast_map[var]
                if isinstance(sub, list) and sub and sub[0] == 'var':
                    arg = expr_to_z3(param_ast_map[var]) # todo: this code is bad
                    # new_arg = fresh_ssa(param_ast_map[var][1])
                    # fresh_ssa(param_ast_map[var][1])
                    # modifies_substitution.append((arg, Int(new_arg)))
                    # modifies_substitution.append((arg, Int(get_ssa(var))))
                    new_arg = fresh_ssa(param_ast_map[var][1])
                    modifies_substitution.append((Int(get_ssa(var)), arg))
                    modifies_substitution.append((arg, Int(new_arg)))
            print("modifies_sub call", modifies_substitution)
            print("post", post)
            # post = substitute(post, *modifies_substitution)
            requires_inst = substitute(requires_inst, *modifies_substitution)
            ensures_inst = substitute(ensures_inst, *modifies_substitution)
            # print("post2", post2)
            # assert(str(post) == str(post2))

            return And(requires_inst, Implies(ensures_inst, post))

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
                canon = _resolve_array_name(name)
                return Array(canon, IntSort(), IntSort())
            # return Int(name)
            return Int(get_ssa(name))
        
        case ['old', [ty, name]]:
            return Int(f"__old_{name}")

        case ['arrvar', name]:
            _array_vars.add(name)
            canon = _resolve_array_name(name)
            return Array(canon, IntSort(), IntSort())

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
    # preprocess functions
    i = 0
    while i < len(stmt):
        if stmt[i][0] == 'proc':
            post = BoolVal(True)
            pre = wp(stmt[i], post)
            del stmt[i]
        else:
            i += 1

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
