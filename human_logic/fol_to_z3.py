from lark import Lark, Transformer
from dataclasses import dataclass

fol_parser = Lark('''start: statement
            statement: "∀" id statement -> forall
                     | "∃" id statement -> exists
                     | id "(" [id ("," id)*] ")" -> pred
                     | "(" statement ")" -> group
                     | "¬" statement -> not_
                     | statement "∧" statement -> and_
                     | statement "∨" statement -> or_
                     | statement "→" statement -> implies
                     | statement "↔" statement -> iff
                     | id -> id
            id: WORD
            %import common.WORD   // imports from terminal library
            %ignore " "           // Disregard spaces in text
         ''')
class MyTransformer(Transformer):
    def id(self, items):
        return IdNode(items[0].value)
    def start(self, items):
        return items[0]
    def exists(self, items):
        return ExistsNode(items[0], items[1])
    def forall(self, items):
        return ForallNode(items[0], items[1])
    def group(self, items):
        return GroupNode(items[0])
    def pred(self, items):
        return PredNode(items[0], items[1:])
    def not_(self, items):
        return NotNode(items[0])
    def and_(self, items):
        return AndNode(items[0], items[1])
    def or_(self, items):
        return OrNode(items[0], items[1])
    def iff(self, items):
        return IffNode(items[0], items[1])
    def implies(self, items):
        return ImpliesNode(items[0], items[1])


class AstNode:
    def visit(self, visitor: 'Visitor'):
        visitor.enter(self)
        for name, value in self.__dict__.items():
            if isinstance(value, AstNode):
                value.visit(visitor)
            elif isinstance(value, list):
                for item in value:
                    if isinstance(item, AstNode):
                        item.visit(visitor)
        visitor.exit(self)

class ExprNode(AstNode):
    pass
                        
class Visitor:
    def enter(self, node: ExprNode):
        pass
    def exit(self, node: ExprNode):
        pass

class UnboundIdCollector(Visitor):
    def __init__(self):
        self.scopes = [set()]
        self.unbound_ids = set()
    def enter(self, node: AstNode):
        if isinstance(node, ExistsNode) or isinstance(node, ForallNode):
            self.scopes.append(set(self.current_scope()))
            self.current_scope().add(node.id.name)
        if isinstance(node, IdNode) and node.name not in self.current_scope():
            self.unbound_ids.add(node.name)

    def exit(self, node: AstNode):
        if isinstance(node, ExistsNode) or isinstance(node, ForallNode):
            self.scopes.pop()
    def current_scope(self):
        return self.scopes[-1]

class FunctionDeclarationCollector(Visitor):
    def __init__(self):
        self.names = set()
        self.declarations = []
    def enter(self, node: AstNode):
        if isinstance(node, PredNode):
            if node.id.name and node.id.name not in self.names:
                self.names.add(node.id.name)
                args_z3 = " ".join(["Obj" for _ in node.args])
                self.declarations.append(f'(declare-fun {node.id.z3()} ({args_z3}) Bool)')


@dataclass
class IdNode(AstNode):
    name: str
    def z3(self):
        return self.name

@dataclass
class ExistsNode(ExprNode):
    id: IdNode
    expr: ExprNode
    def z3(self):
        return f'(exists (({self.id.z3()} Obj)) {self.expr.z3()})'

@dataclass
class GroupNode(ExprNode):
    expr: ExprNode
    def z3(self):
        return self.expr.z3()

@dataclass
class PredNode(ExprNode):
    id: IdNode
    args: list[ExprNode]
    def z3(self):
        return f'({self.id.z3()} {" ".join([arg.z3() for arg in self.args])})'

@dataclass
class ForallNode(ExprNode):
    id: IdNode
    expr: ExprNode
    def z3(self):
        return f'(forall (({self.id.z3()} Obj)) {self.expr.z3()})'

@dataclass
class NotNode(ExprNode):
    expr: ExprNode
    def z3(self):
        return f'(not {self.expr.z3()})'

@dataclass
class AndNode(ExprNode):
    left: ExprNode
    right: ExprNode
    def z3(self):
        return f'(and {self.left.z3()} {self.right.z3()})'

@dataclass
class OrNode(ExprNode):
    left: ExprNode
    right: ExprNode
    def z3(self):
        return f'(or {self.left.z3()} {self.right.z3()})'
@dataclass
class IffNode(ExprNode):
    left: ExprNode
    right: ExprNode
    def z3(self):
        return f'(= {self.left.z3()} {self.right.z3()})'
@dataclass
class ImpliesNode(ExprNode):
    left: ExprNode
    right: ExprNode
    def z3(self):
        return f'(=> {self.left.z3()} {self.right.z3()})'

@dataclass
class Z3Proof:
    declarations: list[str]
    assertions: list[str]
    conclusion: str

    def declarations_z3(self):
        return "\n".join(self.declarations)
    def assertions_z3(self):
        return "\n".join(self.assertions)
    def conclusion_z3(self):
        return self.conclusion

def decl_z3_lines(nodes: ExprNode):
    function_declaration_collector = FunctionDeclarationCollector()
    unbound_id_collector = UnboundIdCollector()
    for node in nodes:
        node.visit(unbound_id_collector)
        node.visit(function_declaration_collector)
    const_names = unbound_id_collector.unbound_ids - function_declaration_collector.names
    const_declarations = [
        f"(declare-const {name} Obj)"
        for name in const_names
    ]
    function_declarations = function_declaration_collector.declarations
    return ["(declare-sort Obj)"] + function_declarations + const_declarations

def z3_assert_wrap(code: str):
    return f"(assert\n  {code})"

def z3_assert_not_wrap(code: str):
    return f"(assert\n  (not {code}))"

def parse_fol(text):
    tree = fol_parser.parse(text)
    # print(tree)
    # print()
    return MyTransformer().transform(tree)

def fol_to_z3(fol_lines: list[str], conclusion: str | None = None):
    expr_nodes = [parse_fol(line) for line in fol_lines]
    assertion_z3_lines = [z3_assert_wrap(node.z3()) for node in expr_nodes]
    conclusion_z3 = ""
    if conclusion:
        conclusion_expr_node = parse_fol(conclusion)
        expr_nodes += [conclusion_expr_node]
        conclusion_z3 = z3_assert_not_wrap(conclusion_expr_node.z3())
    return Z3Proof(
        declarations=decl_z3_lines(expr_nodes),
        assertions=assertion_z3_lines,
        conclusion=conclusion_z3
    )