import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Nat.Le.is.Lt.ou.Eq |
| comm | Nat.Lt.ou.Eq.is.Le |
| mp   | Nat.Lt.ou.Eq.of.Le |
| mpr  | Nat.Le.of.Lt.ou.Eq |
| mp.comm | Nat.Eq.ou.Lt.of.Ge |
-/
@[main, comm, mp, mpr, mp.comm]
private lemma main
  [PartialOrder α]
-- given
  (a b : α) :
-- imply
  a ≤ b ↔ a < b ∨ a = b :=
-- proof
  le_iff_lt_or_eq


-- created on 2025-03-29
-- updated on 2026-07-19
