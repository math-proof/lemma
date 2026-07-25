import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Rat.Eq\_0.is.EqInv\_0 |
| comm | Rat.EqInv\_0.is.Eq\_0 |
| mp | Rat.EqInv\_0.of.Eq\_0 |
| mpr | Rat.Eq\_0.of.EqInv\_0 |
| mp.mt | Rat.Ne\_0.of.NeInv\_0 |
| mpr.mt | Rat.NeInv\_0.of.Ne\_0 |
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
