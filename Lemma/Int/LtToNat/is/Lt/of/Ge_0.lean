import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Int.LtToNat.is.Lt.of.Ge_0 |
| comm | Int.Lt.is.LtToNat.of.Ge_0 |
| mp | Int.Lt.of.LtToNat.Ge_0 |
| mpr | Int.LtToNat.of.Lt.Ge_0 |
-/
@[main, comm, mp, mpr]
private lemma main
  {z : ℤ}
-- given
  (h : 0 ≤ z)
  (n : ℕ) :
-- imply
  z.toNat < n ↔ z < n :=
-- proof
  Int.toNat_lt h


-- created on 2025-08-02
