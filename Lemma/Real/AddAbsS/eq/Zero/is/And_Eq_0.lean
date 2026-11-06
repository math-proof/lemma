import Initialize.Tactic.Attr.Basic


/--
| attributes | lemma |
| :---: | :---: |
| path | Real.AddAbsS.eq.Zero.is.And_Eq_0 |
| comm | Real.And_Eq_0.is.AddAbsS.eq.Zero |
| mp | Real.And_Eq_0.of.AddAbsS.eq.Zero |
| mpr | Real.AddAbsS.eq.Zero.of.And_Eq_0 |
| is.mt | Real.AddAbsS.ne.Zero.is.NotAnd_Eq_0 |
-/
@[path, comm, mp, mpr, is.mt]
private lemma main
-- given
  (A B : ℝ) :
-- imply
  |A| + |B| = 0 ↔ A = 0 ∧ B = 0 := by
-- proof
  rw [add_eq_zero_iff_of_nonneg (abs_nonneg A) (abs_nonneg B), abs_eq_zero, abs_eq_zero]


-- created on 2026-11-04
