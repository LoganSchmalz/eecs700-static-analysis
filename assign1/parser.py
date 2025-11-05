import ast
import pprint

def py_ast(filename):
    with open(filename, "r") as f:
        tree = ast.parse(f.read(), filename=filename)
        return tree

class WhilePyVisitor(ast.NodeVisitor):
    def visit_Module(self, node):
        nodes = list(map(self.visit, node.body))
        return ['seq'] + nodes
    
    def visit_Expr(self, node):
        return self.visit(node.value)
    
    def visit_Call(self, node):
        if isinstance(node.func, ast.Name):
            if node.func.id == 'assume':
                assert len(node.args) == 1
                return ['assume', self.visit(node.args[0])]
            elif node.func.id == 'assert':
                assert len(node.args) == 1
                return ['assert', self.visit(node.args[0])]
            elif node.func.id == 'invariant':
                assert len(node.args) == 1
                return ['invariant', self.visit(node.args[0])]
            elif node.func.id == 'requires':
                assert len(node.args) == 1
                return ['requires', self.visit(node.args[0])]
            elif node.func.id == 'ensures':
                assert len(node.args) == 1
                return ['ensures', self.visit(node.args[0])]
            elif node.func.id == 'modifies':
                assert len(node.args) == 1
                return ['modifies', self.visit(node.args[0])]
            elif node.func.id == 'len':
                assert len(node.args) == 1
                return ['len', self.visit(node.args[0])]
            elif node.func.id == 'old':
                # old(x) -> ['old', <expr>]
                assert len(node.args) == 1
                return ['old', self.visit(node.args[0])]
            else:
                print(node.func.id, list(map(self.visit, node.args)))
                return ['call', node.func.id, list(map(self.visit, node.args))]
        raise NotImplementedError(ast.dump(node))
    
    def visit_Const(self, node):
        assert isinstance(node.value, (int, bool))
        return ['const', node.value]
    
    def visit_Constant(self, node):
        assert isinstance(node.value, (int, bool))
        return ['const', node.value]
    
    def visit_If(self, node):
        test = self.visit(node.test)
        body = list(map(self.visit, node.body))
        orelse = list(map(self.visit, node.orelse))
        if len(orelse) == 0:
            orelse = [['skip']]
        return ['if', test, body, orelse]
    
    def visit_Compare(self, node):
        # support chained comparisons: a < b < c  ->  ['and', ['<', a, b], ['<', b, c]]
        left = self.visit(node.left)
        comparisons = []
        prev = left
        for op, comp in zip(node.ops, node.comparators):
            right = self.visit(comp)
            if isinstance(op, ast.Lt):
                comparisons.append(['<', prev, right])
            elif isinstance(op, ast.LtE):
                comparisons.append(['<=', prev, right])
            elif isinstance(op, ast.Gt):
                comparisons.append(['>', prev, right])
            elif isinstance(op, ast.GtE):
                comparisons.append(['>=', prev, right])
            elif isinstance(op, ast.Eq):
                comparisons.append(['==', prev, right])
            elif isinstance(op, ast.NotEq):
                comparisons.append(['!=', prev, right])
            else:
                raise NotImplementedError(ast.dump(node))
            prev = right

        # if there's only one comparison, return it directly
        if len(comparisons) == 1:
            return comparisons[0]
        # otherwise combine with a top-level 'and' node
        return ['and'] + comparisons
    
    def visit_Name(self, node):
        return ['var', node.id]
    
    def visit_UnaryOp(self, node):
        assert isinstance(node.op, ast.USub)
        operand = self.visit(node.operand)
        return ['-', operand]
    
    def visit_BinOp(self, node):
        left = self.visit(node.left)
        right = self.visit(node.right)
        if isinstance(node.op, ast.Add):
            return ['+', left, right]
        elif isinstance(node.op, ast.Sub):
            return ['-', left, right]
        elif isinstance(node.op, ast.Mult):
            return ['*', left, right]
        elif isinstance(node.op, ast.Div):
            return ['/', left, right]
        else:
            raise NotImplementedError(ast.dump(node))
    
    def visit_Assign(self, node):
        assert len(node.targets) == 1
        target = node.targets[0]
        value = self.visit(node.value)
        if isinstance(target, ast.Name):
            var = target.id
            return ['assign', var, value]
        elif isinstance(target, ast.Subscript):
            arr = self.visit(target.value)
            arr = ['arrvar', arr[1]] # should this override be here?
            index = self.visit(target.slice)
            return ['store', arr, index, value]
        else:
            raise NotImplementedError(ast.dump(target))
    
    def visit_Pass(self, node):
        return ['skip']
    
    def visit_Assert(self, node):
        test = self.visit(node.test)
        return ['assert', test]
    
    def visit_While(self, node):
        test = self.visit(node.test)
        body = list(map(self.visit, node.body))
        invariants = []
        for stmt in node.body:
            if isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Call):
                call = stmt.value
                if isinstance(call.func, ast.Name) and call.func.id == 'invariant':
                    assert len(call.args) == 1
                    inv = self.visit(call.args[0])
                    invariants.append(inv)
        return ['while', test, body, invariants]

    def visit_FunctionDef(self, node):
        name = node.name
        params = [arg.arg for arg in node.args.args]

        requires = []
        ensures = []
        modifies = []
        body = list(map(self.visit, node.body))

        for stmt in node.body:
            # look for top-level require/ensure calls written as Expr(Call(Name, ...))
            if isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Call) and isinstance(stmt.value.func, ast.Name):
                fid = stmt.value.func.id
                if fid == 'requires':
                    assert len(stmt.value.args) == 1
                    requires.append(self.visit(stmt.value.args[0]))
                    continue
                if fid == 'ensures':
                    assert len(stmt.value.args) == 1
                    ensures.append(self.visit(stmt.value.args[0]))
                    continue
                if fid == 'modifies':
                    assert len(stmt.value.args) == 1
                    modifies.append(self.visit(stmt.value.args[0])[1])
                    continue

        return ['proc', name, params, body, requires, ensures, modifies]

    def visit_Return(self, node):
        # represent return as ['return', value] (value may be None)
        if node.value is None:
            return ['return']
        return ['return', self.visit(node.value)]
    
    def generic_visit(self, node):
        raise NotImplementedError(ast.dump(node))
    
    def visit_Subscript(self, node):
        if isinstance(node.value, ast.Name):
            arr = ['arrvar', node.value.id]
        else: # array literal
            arr = self.visit(node.value)
        index = self.visit(node.slice)
        return ['select', arr, index]

    def visit_List(self, node):
        # list literal -> ['array', elem1, elem2, ...]
        elems = [self.visit(elt) for elt in node.elts]
        return ['array'] + elems

    def visit_Tuple(self, node):
        # tuple literal -> treat similarly to list
        elems = [self.visit(elt) for elt in node.elts]
        return ['array'] + elems

# tree = py_ast("parse_example.py")
# visitor = WhilePyVisitor()
# stmt = visitor.visit(tree)
# pprint.pprint(stmt)
