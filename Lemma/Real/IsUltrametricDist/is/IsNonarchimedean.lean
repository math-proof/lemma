import sympy.Basic
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Analysis.Normed.Field.Ultra
import Mathlib.Analysis.Normed.Field.WithAbs
import Mathlib.Analysis.Normed.Module.Completion


/--
[AbsoluteValue_Completion_isUltrametricDist_of_isNonarchimedean](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AbsoluteValue_Completion_isUltrametricDist_of_isNonarchimedean.lean)
-/
@[main, comm, mp, mpr]
private lemma main
  [Field K]
  (v : AbsoluteValue K ℝ) :
-- imply
  IsUltrametricDist v.Completion ↔ IsNonarchimedean v := by
-- proof
  constructor
  ·
    intro hv a b
    have h := hv.dist_triangle_max
      (x := ((a + b : K) : v.Completion))
      (y := ((b : K) : v.Completion))
      (z := ((0 : K) : v.Completion))
    simp only [UniformSpace.Completion.dist_eq] at h
    simp only [dist_eq_norm] at h
    simp only [WithAbs.norm_eq_apply_ofAbs] at h
    simp only [WithAbs.ofAbs_sub] at h
    simpa using h
  ·
    intro hv
    refine IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one fun n => ?_
    have h1 : ((n : WithAbs v) : v.Completion) = (n : v.Completion) :=
      map_natCast UniformSpace.Completion.coeRingHom n
    have h2 : (n : WithAbs v).ofAbs = (n : K) := map_natCast (WithAbs.equiv v) n
    rw [← h1, UniformSpace.Completion.norm_coe, WithAbs.norm_eq_apply_ofAbs, h2]
    exact IsNonarchimedean.apply_natCast_le_one hv


-- created on 2026-09-18
