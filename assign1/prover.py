from z3 import *

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
            return substitute(post, (Int(var), expr_z3))

        case ['invariant', *rest]:
            # invariants do not affect the weakest precondition
            return BoolVal(True)

        case ['while', cond, body, invariants]:
            cond_z3 = expr_to_z3(cond)
            invariant = And(*list(map(expr_to_z3, invariants)))
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
            return Int(name)

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
