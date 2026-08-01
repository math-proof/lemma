import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Nat.Ge_Max.is.Ge.Ge |
| comm | Nat.Ge.Ge.is.Ge_Max |
| mp | Nat.Ge.Ge.of.Ge_Max |
| mpr | Nat.Ge_Max.of.Ge.Ge |
-/
@[main, comm, mp, mpr]
private lemma main
  [LinearOrder α]
-- given
  (x a b : α) :
-- imply
  x ≥ a ⊔ b ↔ x ≥ a ∧ x ≥ b := by
-- proof
  constructor <;>
  · 
    intros
    simp_all


-- created on 2025-09-29
