import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Rat.Eq.is.EqInv |
| comm | Rat.EqInv.is.Eq |
| mp | Rat.EqInv.of.Eq |
| mpr | Rat.Eq.of.EqInv |
| mp.mt | Rat.Ne.of.NeInv |
| mpr.mt | Rat.NeInv.of.Ne |
-/
@[main, comm, mp, mpr, mp.mt, mpr.mt]
private lemma main
  [GroupWithZero α]
-- given
  (a b : α) :
-- imply
  a = b⁻¹ ↔ a⁻¹ = b := by
-- proof
  constructor <;>
  .
    intro h
    have := congrArg (fun x => x⁻¹) h
    simp at this
    assumption



-- created on 2026-07-26
