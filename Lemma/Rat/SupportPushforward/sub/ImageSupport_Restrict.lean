import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_AlgebraicCurve_DivisorPushPull
import Lemma.Int.P2MUtil

open AlgebraicCurve AlgebraicCurve.Divisor

/--
[AlgebraicCurve_Divisor_support_pushforward_subset](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_Divisor_support_pushforward_subset.lean)
-/
@[path]
private lemma main
  {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] [DecidableEq (Place K F)]
  {D : Divisor K F'} :
-- imply
  (Divisor.pushforward F D).support ⊆ D.support.image (fun w => w.restrict F) := by
-- proof
  classical
  intro v hv
  rw [Finsupp.mem_support_iff, pushforward_apply] at hv
  obtain ⟨w, hw, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hv
  refine Finset.mem_image.mpr ⟨w, hw, ?_⟩
  by_contra h
  exact hne (ite_eq_right h)


-- created on 2026-10-23
