import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Nat.NotLt.is.Ge |
| comm | Nat.Ge.is.NotLt |
| mp | Nat.Ge.of.NotLt |
| mp.comm | Nat.Le.of.NotGt |
-/
@[main, comm, mp, mp.comm]
private lemma main
  [LinearOrder α]
  {a b : α} :
-- imply
  ¬a < b ↔ a ≥ b :=
-- proof
  not_lt


-- created on 2025-04-18
