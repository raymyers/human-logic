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
    try: 
        z3_proof = fol_to_z3(expressions, conclusion)
    except Exception as e:
        return (False, f"{e}", "")
    return check_z3_proof(z3_proof)

def check_z3_proof(z3_proof: Z3Proof) -> tuple[bool, str, str]:
    z3_code = z3_proof.all_z3()
    try:
        solver = z3.Solver()
        solver.from_string(z3_proof.declarations_z3())
        for assertion in z3_proof.assertions:
            solver.from_string(assertion)
            if solver.check() != z3.sat:
                return (False, f"Assertions unsatisfiable on line `{assertion}`", z3_code)
        if z3_proof.conclusion:
            solver.from_string(z3_proof.conclusion_z3())
            if solver.check() == z3.sat:
                return (False, "Negated conclusion is satifiable, proof rejected", z3_code)
            if solver.check() == z3.unknown:
                return (False, "Negated conclusion has unknown satisfiability, proof rejected", z3_code)
        return (True, "OK", z3_code)
    except z3.Z3Exception as e:
        return (False, f"Z3 exception {e}", z3_code)
