import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.DifferentialAnalysis.code.SchwartzCutoffConvergence
open Filter Topology Metric SchwartzMap
open scoped NNReal


namespace SchwartzMap

/--
[bumpSeq_rIn](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzCutoffConvergence.lean)
-/
@[path]
lemma bumpSeq_rIn
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {m : ℕ} :
-- imply
  (bumpSeq (E := E) m).rIn = ↑m + 1 :=
-- proof
  rfl

end SchwartzMap

namespace SchwartzMap

/--
[bumpSeq_rOut](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzCutoffConvergence.lean)
-/
@[path]
lemma bumpSeq_rOut
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {m : ℕ} :
-- imply
  (bumpSeq (E := E) m).rOut = ↑m + 2 :=
-- proof
  rfl

end SchwartzMap

namespace SchwartzMap

/--
[bumpSeq_one_of_norm_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzCutoffConvergence.lean)
-/
@[path]
lemma bumpSeq_one_of_norm_le
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {m : ℕ}
  {x : E}
-- given
  (hx : ‖x‖ ≤ ↑m + 1) :
-- imply
  bumpSeq (E := E) m x = 1 := by
-- proof
  apply ContDiffBump.one_of_mem_closedBall
  simp only [Metric.mem_closedBall, dist_zero_right]
  exact hx

end SchwartzMap

namespace SchwartzMap

/--
[bumpSeq_hasTemperateGrowth](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzCutoffConvergence.lean)
-/
@[path]
lemma bumpSeq_hasTemperateGrowth
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {m : ℕ} :
-- imply
  Function.HasTemperateGrowth (fun x => (bumpSeq (E := E) m x : ℝ)) :=
-- proof
  HasCompactSupport.hasTemperateGrowth (bumpSeq m).hasCompactSupport (bumpSeq m).contDiff

end SchwartzMap

namespace SchwartzMap

/--
[bumpCutoffMul_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzCutoffConvergence.lean)
-/
@[path]
lemma bumpCutoffMul_apply
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {m : ℕ}
  {f : SchwartzMap E F}
  {x : E} :
-- imply
  bumpCutoffMul m f x = bumpSeq (E := E) m x • f x := by
-- proof
  unfold bumpCutoffMul
  rw [SchwartzMap.smulLeftCLM_apply (bumpSeq_hasTemperateGrowth m)]

end SchwartzMap

namespace SchwartzMap

/--
[bumpCutoffMul_hasCompactSupport](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzCutoffConvergence.lean)
-/
@[path]
lemma bumpCutoffMul_hasCompactSupport
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {m : ℕ}
  {f : SchwartzMap E F} :
-- imply
  HasCompactSupport (bumpCutoffMul m f) := by
-- proof
  apply HasCompactSupport.of_support_subset_isCompact (K := Metric.closedBall 0 (↑m + 2))
    (isCompact_closedBall 0 _)
  intro x hx
  rw [Function.mem_support] at hx
  simp only [bumpCutoffMul_apply] at hx
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra h
  push Not at h
  have hout : (bumpSeq (E := E) m).rOut ≤ dist x 0 := by
    rw [dist_zero_right]; simp only [bumpSeq]; linarith
  have := (bumpSeq m).zero_of_le_dist hout
  simp [this] at hx

end SchwartzMap

namespace SchwartzMap

/--
[sub_bumpCutoffMul_eventuallyEq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzCutoffConvergence.lean)
-/
@[path]
lemma sub_bumpCutoffMul_eventuallyEq_zero
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {m : ℕ}
  {f : SchwartzMap E F}
  {x : E}
-- given
  (hx : ‖x‖ < ↑m + 1) :
-- imply
  (fun y => (f - bumpCutoffMul m f) y) =ᶠ[nhds x] (fun _ => (0 : F)) := by
-- proof
  have hmem : x ∈ Metric.ball (0 : E) (bumpSeq (E := E) m).rIn := by
    simp only [Metric.mem_ball, dist_zero_right, bumpSeq]; exact hx
  have hev := (bumpSeq (E := E) m).eventuallyEq_one_of_mem_ball hmem
  filter_upwards [hev] with y hy
  simp only [SchwartzMap.sub_apply, bumpCutoffMul_apply, Pi.one_apply] at hy ⊢
  rw [hy, one_smul, sub_self]

end SchwartzMap

namespace SchwartzMap

/--
[iteratedFDeriv_sub_bumpCutoffMul_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzCutoffConvergence.lean)
-/
@[path]
lemma iteratedFDeriv_sub_bumpCutoffMul_eq_zero
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {m : ℕ}
  {f : SchwartzMap E F}
  {n : ℕ}
  {x : E}
-- given
  (hx : ‖x‖ < ↑m + 1) :
-- imply
  iteratedFDeriv ℝ n (fun y => (f - bumpCutoffMul m f) y) x = 0 := by
-- proof
  have hev := sub_bumpCutoffMul_eventuallyEq_zero m f hx
  have h := (hev.iteratedFDeriv ℝ n).self_of_nhds
  rw [h]
  obtain rfl | hn := eq_or_ne n 0
  · ext v; simp
  · simp [iteratedFDeriv_const_of_ne hn (0 : F)]

end SchwartzMap

/--
[SchwartzMap.seminorm_le_div_of_vanish](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzCutoffConvergence.lean)
-/
@[path]
lemma SchwartzMap.seminorm_le_div_of_vanish
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  {𝕜 : Type*}
  [NormedField 𝕜]
  [NormedSpace 𝕜 F]
  [SMulCommClass ℝ 𝕜 F]
  {g : SchwartzMap E F}
  {k j : ℕ}
  {R : ℝ}
-- given
  (hR : 0 < R)
  (hvanish : ∀ x : E, ‖x‖ < R → iteratedFDeriv ℝ j (⇑g) x = 0) :
-- imply
  (SchwartzMap.seminorm 𝕜 k j) g ≤ (SchwartzMap.seminorm 𝕜 (k + 1) j) g / R := by
-- proof
  rw [div_eq_inv_mul]
  apply SchwartzMap.seminorm_le_bound 𝕜 k j g (by positivity)
  intro x
  by_cases hx : ‖x‖ < R
  · rw [hvanish x hx, norm_zero, mul_zero]; positivity
  · push Not at hx
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ j (⇑g) x‖
      = R⁻¹ * (R * ‖x‖ ^ k) * ‖iteratedFDeriv ℝ j (⇑g) x‖ := by
        rw [inv_mul_cancel_left₀ (ne_of_gt hR)]
      _ ≤ R⁻¹ * (‖x‖ * ‖x‖ ^ k) * ‖iteratedFDeriv ℝ j (⇑g) x‖ := by
        gcongr
      _ = R⁻¹ * (‖x‖ ^ (k + 1) * ‖iteratedFDeriv ℝ j (⇑g) x‖) := by
        rw [pow_succ]; ring
      _ ≤ R⁻¹ * (SchwartzMap.seminorm 𝕜 (k + 1) j) g := by
        gcongr; exact SchwartzMap.le_seminorm 𝕜 (k + 1) j g x
/-- Iterated Fréchet derivatives of a `ContDiffBump` on `E` admit a uniform bound `C`
depending only on the order `n` and the ratio `rOut/rIn`. -/
namespace SchwartzMap
/-- Cutoff convergence (Melrose Lemma 8.8): every Schwartz seminorm of `f - χ_m f`
tends to `0` as `m → ∞`, hence `χ_m f → f` in the Schwartz topology. -/
end SchwartzMap


-- created on 2026-10-23
