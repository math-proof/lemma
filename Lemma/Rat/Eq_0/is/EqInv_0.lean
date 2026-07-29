import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Rat.Eq_0.is.EqInv_0 |
| comm | Rat.EqInv_0.is.Eq_0 |
| mp | Rat.EqInv_0.of.Eq_0 |
| mpr | Rat.Eq_0.of.EqInv_0 |
| mp.mt | Rat.Ne_0.of.NeInv_0 |
| mpr.mt | Rat.NeInv_0.of.Ne_0 |
-/
@[main, comm, mp, mpr, mp.mt, mpr.mt]
private lemma main
  [GroupWithZero α]
-- given
  (a : α) :
-- imply
  a = 0 ↔ a⁻¹ = 0 := by
-- proof
  simp_all


-- created on 2026-07-08
