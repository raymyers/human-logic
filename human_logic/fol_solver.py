import z3

from human_logic.fol_to_z3 import fol_to_z3, Z3Proof

# expressions = [
#     "∃x (Logic(x) ∧ Easy(x))",
#     "∀x(Math(x) → Hard(x))",
#     "¬∃x(Fun(x) ∧ Useless(x))",
#     "∃x(Art(x) ∨ Science(x))",
#     "∀x((Student(x) ∧ Sleepy(x)) → Fails(x))",
#     "∀x(Teacher(x) ↔ Wise(x))",
#     "∀x∃y(Friend(x, y) ∧ Trusts(x, y))",
#     "∀x∀y((Parent(x, y) ∧ Child(y, x)) → Loves(x, y))",
#     "∀x¬(Boring(x) ∧ Easy(x))"
# ]
# conclusion = "∀x(Teacher(x) ∨ ¬Teacher(x))"


def check_fol_proof(expressions: list[str], conclusion: str | None):
    z3_proof = fol_to_z3(expressions, conclusion)
    return check_z3_proof(z3_proof)

def check_z3_proof(z3_proof: Z3Proof) -> tuple[bool, str]:
    try:
        solver = z3.Solver()
        solver.from_string(z3_proof.declarations_z3())
        for assertion in z3_proof.assertions:
            solver.from_string(assertion)
            if solver.check() != z3.sat:
                return (False, f"Assertions unsatisfiable on line `{assertion}`")
        if z3_proof.conclusion:
            solver.from_string(z3_proof.conclusion_z3())
            if solver.check() == z3.sat:
                return (False, "Negated conclusion is satifiable, proof rejected")
            if solver.check() == z3.unknown:
                return (False, "Negated conclusion has unknown satisfiability, proof rejected")
        return (True, "OK")
    except z3.Z3Exception as e:
        return (False, f"Z3 exception {e}")
