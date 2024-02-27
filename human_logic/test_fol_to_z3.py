from human_logic.fol_to_z3 import parse_fol, decl_z3_lines, UnboundIdCollector


def test_decl_z3_lines_declares_functions():
    node = parse_fol("∀ x (Man(x) → Mortal(x))")
    assert decl_z3_lines([node]) == [
        '(declare-sort Obj)',
        '(declare-fun Man (Obj) Bool)',
        '(declare-fun Mortal (Obj) Bool)'
    ]

def test_decl_z3_lines_declares_functions_only_once():
    node1 = parse_fol("∀ x (Man(x) → Mortal(x))")
    node2 = parse_fol("∀ x (Man(x) → Mortal(x))")
    assert decl_z3_lines([node1, node2]) == [
        '(declare-sort Obj)',
        '(declare-fun Man (Obj) Bool)',
        '(declare-fun Mortal (Obj) Bool)'
    ]


def test_constant_extraction():
    node = parse_fol("Man(Socrates)")
    print(node)
    unbound_id_collector = UnboundIdCollector()
    node.visit(unbound_id_collector)
   
    assert unbound_id_collector.unbound_ids == {"Man","Socrates"}

def test_decl_z3_lines_declares_constant():
    node = parse_fol("Man(Socrates)")
    print(node)
    assert decl_z3_lines([node]) == [
        '(declare-sort Obj)',
        '(declare-fun Man (Obj) Bool)',
        '(declare-const Socrates Obj)'
    ]

def test_parse_double_forall():
    node = parse_fol("∀ A ∀ B (Cause(A, B) → (¬A → ¬B))")

    assert node

