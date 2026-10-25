import Mathlib
import sympy.Basic
import Def.v1.Atlas.AnAlgorithmistsToolkit.code.SurfaceArea
open Pointwise MeasureTheory Set Filter SurfaceArea


namespace SurfaceArea

/--
[minkowskiThickening_unitBall_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/SurfaceArea.lean)
-/
@[path]
lemma minkowskiThickening_unitBall_eq
  {n : ℕ}
  {n : ℕ}
-- given
  (hε : 0 ≤ ε) :
-- imply
  minkowskiThickening (unitBall n) ε = Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 + ε) := by
-- proof
  unfold minkowskiThickening unitBall
  rw [smul_unitClosedBall_of_nonneg hε]
  rw [closedBall_add_closedBall (by norm_num : (0 : ℝ) ≤ 1) hε 0 0]
  simp

end SurfaceArea

namespace SurfaceArea

/--
[minkowskiThickening_unitBall_eq_smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/SurfaceArea.lean)
-/
@[path]
lemma minkowskiThickening_unitBall_eq_smul
  {n : ℕ}
  {n : ℕ}
-- given
  (hε : 0 ≤ ε) :
-- imply
  minkowskiThickening (unitBall n) ε = (1 + ε) • unitBall n := by
-- proof
  rw [minkowskiThickening_unitBall_eq hε]
  unfold unitBall
  rw [← smul_unitClosedBall_of_nonneg (by linarith : (0 : ℝ) ≤ 1 + ε)]

end SurfaceArea

namespace SurfaceArea

/--
[volume_minkowskiThickening_unitBall](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/SurfaceArea.lean)
-/
@[path]
lemma volume_minkowskiThickening_unitBall
  {n : ℕ}
  {n : ℕ}
-- given
  (hε : 0 ≤ ε) :
-- imply
  (volume (minkowskiThickening (unitBall n) ε)).toReal = (1 + ε) ^ n * (volume (unitBall n)).toReal := by
-- proof
  rw [minkowskiThickening_unitBall_eq_smul hε]
  unfold unitBall
  rw [MeasureTheory.Measure.addHaar_smul_of_nonneg volume (by linarith : (0 : ℝ) ≤ 1 + ε)]
  rw [finrank_euclideanSpace_fin (𝕜 := ℝ)]
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg (by linarith : (0 : ℝ) ≤ 1 + ε) n)]

end SurfaceArea

namespace SurfaceArea

/--
[surfaceArea_unitBall_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/SurfaceArea.lean)
-/
@[path]
lemma surfaceArea_unitBall_eq
  {n : ℕ}
  {n : ℕ}
-- given
  (_hn : 2 ≤ n)
  (_hVB_pos : 0 < (volume (unitBall n)).toReal) :
-- imply
  surfaceArea (unitBall n) = ↑n * (volume (unitBall n)).toReal := by
-- proof
  unfold surfaceArea
  have htendsto : Filter.Tendsto
    (fun ε => ((volume (minkowskiThickening (unitBall n) ε)).toReal -
      (volume (unitBall n)).toReal) / ε)
    (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (↑n * (volume (unitBall n)).toReal)) := by
    have heq : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Ioi 0),
      ((volume (minkowskiThickening (unitBall n) ε)).toReal -
        (volume (unitBall n)).toReal) / ε =
      ((1 + ε) ^ n - 1) / ε * (volume (unitBall n)).toReal := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε_nn : (0 : ℝ) ≤ ε := le_of_lt hε
      rw [volume_minkowskiThickening_unitBall hε_nn]
      ring
    have hder : HasDerivAt (fun ε : ℝ => (1 + ε) ^ n) (↑n : ℝ) 0 := by
      have h1 : HasDerivAt (fun ε : ℝ => 1 + ε) 1 0 :=
        (hasDerivAt_id 0).const_add 1
      have h2 := h1.pow n
      have h3 : (↑n : ℝ) * (1 + (0 : ℝ)) ^ (n - 1) * 1 = (↑n : ℝ) := by
        simp [one_pow]
      rwa [h3] at h2
    have hslope' := hder.tendsto_slope_zero_right
    have hslope : Filter.Tendsto (fun ε : ℝ => ((1 + ε) ^ n - 1) / ε)
      (nhdsWithin 0 (Ioi 0)) (nhds (↑n : ℝ)) := by
      refine Filter.Tendsto.congr ?_ hslope'
      intro t
      simp [div_eq_inv_mul, smul_eq_mul, zero_add]
    have hmul : Filter.Tendsto (fun ε : ℝ => ((1 + ε) ^ n - 1) / ε * (volume (unitBall n)).toReal)
      (nhdsWithin 0 (Ioi 0)) (nhds (↑n * (volume (unitBall n)).toReal)) :=
      hslope.mul tendsto_const_nhds
    have heq_symm : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Ioi 0),
      ((1 + ε) ^ n - 1) / ε * (volume (unitBall n)).toReal =
      ((volume (minkowskiThickening (unitBall n) ε)).toReal -
        (volume (unitBall n)).toReal) / ε := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε_nn : (0 : ℝ) ≤ ε := le_of_lt hε
      rw [volume_minkowskiThickening_unitBall hε_nn]
      ring
    exact Filter.Tendsto.congr' heq_symm hmul
  exact htendsto.limUnder_eq

end SurfaceArea


-- created on 2026-10-23
