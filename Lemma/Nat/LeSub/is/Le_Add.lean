import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Nat.LeSub.is.Le_Add |
| comm | Nat.Le_Add.is.LeSub |
| mp   | Nat.Le_Add.of.LeSub |
| mpr  | Nat.LeSub.of.Le_Add |
| mp.comm | Nat.GeAdd.of.Ge_Sub |
| mpr.comm | Nat.Ge_Sub.of.GeAdd |
| comm.is | Nat.Ge_Sub.is.GeAdd |
-/
@[main, comm, mp, mpr, mp.comm, mpr.comm, comm.is]
private lemma main
-- given
  (a b c : ℕ) :
-- imply
  c - b ≤ a ↔ c ≤ a + b :=
-- proof
  Nat.sub_le_iff_le_add


@[main, comm, mp, mpr, mp.comm, mpr.comm, comm.is]
private lemma left
-- given
  (a b c : ℕ) :
-- imply
  c - a ≤ b ↔ c ≤ a + b :=
-- proof
  Nat.sub_le_iff_le_add'


-- created on 2024-11-27
-- updated on 2025-10-16
