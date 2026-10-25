import Mathlib
import sympy.Basic
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter4.Def_4_7
open Matrix Real


/--
[IsSpikedCovariance.posSemidef](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Def_4_7.lean)
-/
@[path]
lemma IsSpikedCovariance.posSemidef
  {d : ℕ}
  {S : Matrix (Fin d) (Fin d) ℝ}
  {θ : ℝ}
  {v : EuclideanSpace ℝ (Fin d)}
-- given
  (h : IsSpikedCovariance S θ v) :
-- imply
  S.PosSemidef := by
-- proof
  obtain ⟨hθ, _, hS⟩ := h
  rw [hS]
  apply PosSemidef.add
  · have : vecMulVec (v : Fin d → ℝ) v = vecMulVec v (star v) := by
    simp [star_trivial]
    rw [this]
    exact (posSemidef_vecMulVec_self_star v).smul (le_of_lt hθ)
  · exact PosSemidef.one

/--
[IsSpikedCovariance.isHermitian](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Def_4_7.lean)
-/
@[path]
lemma IsSpikedCovariance.isHermitian
  {d : ℕ}
  {S : Matrix (Fin d) (Fin d) ℝ}
  {θ : ℝ}
  {v : EuclideanSpace ℝ (Fin d)}
-- given
  (h : IsSpikedCovariance S θ v) :
-- imply
  S.IsHermitian :=
-- proof
  h.posSemidef.isHermitian

/--
[dotProduct_self_eq_one_of_norm_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Def_4_7.lean)
-/
@[path]
lemma dotProduct_self_eq_one_of_norm_eq_one
  {d : ℕ}
  {v : EuclideanSpace ℝ (Fin d)}
-- given
  (hv : ‖v‖ = 1) :
-- imply
  (v : Fin d → ℝ) ⬝ᵥ v = 1 := by
-- proof
  have h1 : @inner ℝ _ _ v v = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, hv, one_pow]
  rwa [show (v : Fin d → ℝ) ⬝ᵥ v = @inner ℝ _ _ v v from by simp [inner, dotProduct]]

/--
[IsSpikedCovariance.mulVec_spike](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Def_4_7.lean)
-/
@[path]
lemma IsSpikedCovariance.mulVec_spike
  {d : ℕ}
  {S : Matrix (Fin d) (Fin d) ℝ}
  {θ : ℝ}
  {v : EuclideanSpace ℝ (Fin d)}
-- given
  (h : IsSpikedCovariance S θ v) :
-- imply
  S.mulVec v = (1 + θ) • v := by
-- proof
  obtain ⟨_, hv, hS⟩ := h
  rw [hS]
  simp only [add_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec]
  rw [dotProduct_self_eq_one_of_norm_eq_one hv]
  ext i
  simp [add_comm, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  ring

/--
[principalAngle_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Def_4_7.lean)
-/
@[path]
lemma principalAngle_nonneg
  {d : ℕ}
  {u v : EuclideanSpace ℝ (Fin d)} :
-- imply
  0 ≤ principalAngle u v :=
-- proof
  arccos_nonneg _

/--
[principalAngle_le_pi](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Def_4_7.lean)
-/
@[path]
lemma principalAngle_le_pi
  {d : ℕ}
  {u v : EuclideanSpace ℝ (Fin d)} :
-- imply
  principalAngle u v ≤ π :=
-- proof
  arccos_le_pi _

/--
[principalAngle_le_pi_div_two](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Def_4_7.lean)
-/
@[path]
lemma principalAngle_le_pi_div_two
  {d : ℕ}
  {u v : EuclideanSpace ℝ (Fin d)} :
-- imply
  principalAngle u v ≤ π / 2 := by
-- proof
  unfold principalAngle
  rw [show π / 2 = arccos 0 from by simp [arccos_zero]]
  exact arccos_le_arccos (abs_nonneg _)

/--
[principalAngle_comm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Def_4_7.lean)
-/
@[path]
lemma principalAngle_comm
  {d : ℕ}
  {u v : EuclideanSpace ℝ (Fin d)} :
-- imply
  principalAngle u v = principalAngle v u := by
-- proof
  unfold principalAngle
  congr 1
  rw [abs_eq_abs]
  left
  exact (real_inner_comm u v).symm


-- created on 2026-10-23
