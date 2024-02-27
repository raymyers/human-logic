from human_logic.fol_solver import check_fol_proof


def test_fol_proof_basic():
    valid, reason, _ = check_fol_proof(["∀ x (Man(x) → Mortal(x))", "Man(Socrates)"], "Mortal(Socrates)")
    assert valid, reason

def test_fol_proof_invalid():
    valid, _, _ = check_fol_proof(["∀ x (Man(x) → Mortal(x))", "Mortal(Socrates)"], "Man(Socrates)")
    assert not valid

def test_fol_declare_in_conclusion():
    valid, reason, _ = check_fol_proof([], "Mortal(Socrates) ∨ ¬Mortal(Socrates)")
    assert valid, reason

def test_no_arg_predicate():
    check_fol_proof(["∃ c (Cause(c) ∧ ¬Effect(c)) ∨ InfiniteRegress()"], None)