import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Nat.NotLe.is.Gt |
| comm | Nat.Gt.is.NotLe |
| mp | Nat.Gt.of.NotLe |
| mp.comm | Nat.Lt.of.NotGe |
-/
@[main, comm, mp, mp.comm]
private lemma main
  [LinearOrder α]
  {a b : α} :
-- imply
  ¬(a ≤ b) ↔ a > b :=
-- proof
  not_le


-- created on 2025-03-29
-- updated on 2025-03-30
