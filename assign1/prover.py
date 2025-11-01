from z3 import *

# track variable names that should be treated as arrays
_array_vars = set()

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

        case ['assign', var, expr]:
            expr_z3 = expr_to_z3(expr)

            is_array_assign = False
            if isinstance(expr, list) and expr and expr[0] == 'array':
                is_array_assign = True
            if isinstance(expr, list) and expr and expr[0] == 'var' and expr[1] in _array_vars:
                is_array_assign = True
            if isinstance(expr, list) and expr and expr[0] == 'arrvar':
                is_array_assign = True

            if var in _array_vars or is_array_assign:
                _array_vars.add(var)
                return substitute(post, (Array(var, IntSort(), IntSort()), expr_z3))
            else:
                return substitute(post, (Int(var), expr_z3))

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

        case _:
            raise NotImplementedError(expr)


def prove(stmt):
    post = BoolVal(True)
    pre = wp(stmt, post)
    print(pre)
    s = Solver()
    s.add(Not(pre))
    if s.check() == unsat:
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
