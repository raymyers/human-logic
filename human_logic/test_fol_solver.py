from human_logic.fol_solver import check_fol_proof


def test_fol_proof_basic():
    valid, reason = check_fol_proof(["∀ x (Man(x) → Mortal(x))", "Man(Socrates)"], "Mortal(Socrates)")
    assert valid, reason

def test_fol_proof_invalid():
    valid, reason = check_fol_proof(["∀ x (Man(x) → Mortal(x))", "Mortal(Socrates)"], "Man(Socrates)")
    assert not valid

def test_fol_declare_in_conclusion():
    valid, reason = check_fol_proof([], "Mortal(Socrates) ∨ ¬Mortal(Socrates)")
    assert valid, reason