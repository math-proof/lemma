import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.FourierAnalysis.code.CentralLimitTheorem
open CentralLimitTheorem
open Complex Finset
open MeasureTheory ProbabilityTheory Filter
open scoped Topology


namespace CentralLimitTheorem

/--
[norm_ofReal_mul_I](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/FourierAnalysis/code/CentralLimitTheorem.lean)
-/
@[path]
lemma norm_ofReal_mul_I
  {x : ℝ} :
-- imply
  ‖(↑x * I : ℂ)‖ = := by
-- proof
  rw [norm_mul, norm_real, norm_I, mul_one, Real.norm_eq_abs]

end CentralLimitTheorem

namespace CentralLimitTheorem

/--
[expTaylorRemainder_le_cube](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/FourierAnalysis/code/CentralLimitTheorem.lean)
-/
@[path]
lemma expTaylorRemainder_le_cube
  {x : ℝ}
-- given
  (hx : |x| ≤ 1) :
-- imply
  ‖expTaylorRemainder x‖ ≤ := by
-- proof
  have key : expTaylorRemainder x =
    cexp (↑x * I) - ∑ m ∈ range 3, (↑x * I) ^ m / (m.factorial : ℂ) := by
    unfold expTaylorRemainder
    simp [sum_range_succ, Nat.factorial]
    ring
  rw [key]
  have hix : ‖(↑x * I : ℂ)‖ ≤ 1 := by rw [norm_ofReal_mul_I]; exact hx
  have h := exp_bound hix (n := 3) (by norm_num)
  rw [norm_ofReal_mul_I] at h
  calc ‖cexp (↑x * I) - ∑ m ∈ range 3, (↑x * I) ^ m / ↑m.factorial‖
    ≤ |x| ^ 3 * ((4 : ℝ) * ((6 : ℝ) * 3)⁻¹) := h
    _ ≤ |x| ^ 3 * 1 := by gcongr; norm_num
    _ = |x| ^ 3 := mul_one _

end CentralLimitTheorem

namespace CentralLimitTheorem

/--
[expTaylorRemainder_le_sq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/FourierAnalysis/code/CentralLimitTheorem.lean)
-/
@[path]
lemma expTaylorRemainder_le_sq
  {x : ℝ}
-- given
  (hx : 1 ≤ |x|) :
-- imply
  ‖expTaylorRemainder x‖ ≤ 4 * := by
-- proof
  unfold expTaylorRemainder
  have hexp : ‖cexp (↑x * I)‖ = 1 := norm_exp_ofReal_mul_I x
  calc ‖cexp (↑x * I) - 1 - ↑x * I - (↑x * I) ^ 2 / 2‖
    ≤ ‖cexp (↑x * I)‖ + ‖(1 : ℂ)‖ + ‖(↑x * I : ℂ)‖ + ‖((↑x * I) ^ 2 / 2 : ℂ)‖ := by
      calc _ ≤ ‖cexp (↑x * I) - 1 - ↑x * I‖ + ‖(↑x * I) ^ 2 / 2‖ := norm_sub_le _ _
        _ ≤ (‖cexp (↑x * I) - 1‖ + ‖↑x * I‖) + ‖(↑x * I) ^ 2 / 2‖ := by
          gcongr; exact norm_sub_le _ _
        _ ≤ (‖cexp (↑x * I)‖ + ‖(1 : ℂ)‖ + ‖↑x * I‖) + ‖(↑x * I) ^ 2 / 2‖ := by
          gcongr; exact norm_sub_le _ _
        _ = _ := by ring
    _ = 2 + |x| + |x| ^ 2 / 2 := by
      rw [hexp, norm_one, norm_ofReal_mul_I, norm_div, norm_pow, norm_ofReal_mul_I, norm_ofNat]
      ring
    _ ≤ 4 * |x| ^ 2 := by nlinarith [sq_nonneg (|x| - 1)]

end CentralLimitTheorem

namespace CentralLimitTheorem

/--
[expTaylorRemainder_le_min](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/FourierAnalysis/code/CentralLimitTheorem.lean)
-/
@[path]
lemma expTaylorRemainder_le_min
  {x : ℝ} :
-- imply
  ‖expTaylorRemainder x‖ ≤ 4 * min (|x| ^ 2) (|x| ^ 3) := by
-- proof
  by_cases hx : |x| ≤ 1
  ·
    have hmin : min (|x| ^ 2) (|x| ^ 3) = |x| ^ 3 := by
      rw [min_eq_right]
      calc |x| ^ 3 = |x| ^ 2 * |x| := by ring
        _ ≤ |x| ^ 2 * 1 := by gcongr
        _ = |x| ^ 2 := mul_one _
    rw [hmin]
    calc ‖expTaylorRemainder x‖ ≤ |x| ^ 3 := expTaylorRemainder_le_cube hx
      _ ≤ 1 * |x| ^ 3 := (one_mul _).symm.le
      _ ≤ 4 * |x| ^ 3 := by gcongr; norm_num
  ·
    have hx' : 1 ≤ |x| := (not_le.mp hx).le
    have hmin : min (|x| ^ 2) (|x| ^ 3) = |x| ^ 2 := by
      rw [min_eq_left]
      calc |x| ^ 2 = |x| ^ 2 * 1 := (mul_one _).symm
        _ ≤ |x| ^ 2 * |x| := by gcongr
        _ = |x| ^ 3 := by ring
    rw [hmin]
    exact expTaylorRemainder_le_sq hx'

end CentralLimitTheorem

namespace CentralLimitTheorem

/--
[min_pow_le_rpow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/FourierAnalysis/code/CentralLimitTheorem.lean)
-/
@[path]
lemma min_pow_le_rpow
  {x : ℝ}
  {α : ℝ}
-- given
  (hα1 : 0 < α)
  (hα2 : α < 1) :
-- imply
  min (|x| ^ 2) (|x| ^ 3) ≤ := by
-- proof
  by_cases hx : |x| ≤ 1
  · calc min (|x| ^ 2) (|x| ^ 3) ≤ |x| ^ 3 := min_le_right _ _
    _ = |x| ^ ((3 : ℕ) : ℝ) := (Real.rpow_natCast |x| 3).symm
    _ ≤ |x| ^ (2 + α) := by
      apply Real.rpow_le_rpow_of_exponent_ge' (abs_nonneg x) hx (by linarith)
      push_cast; linarith
  · have hx' : 1 ≤ |x| := (not_le.mp hx).le
    calc min (|x| ^ 2) (|x| ^ 3) ≤ |x| ^ 2 := min_le_left _ _
      _ = |x| ^ ((2 : ℕ) : ℝ) := (Real.rpow_natCast |x| 2).symm
      _ ≤ |x| ^ (2 + α) := by
        apply Real.rpow_le_rpow_of_exponent_le hx'
        push_cast; linarith

end CentralLimitTheorem

namespace CentralLimitTheorem

/--
[expTaylorRemainder_le_rpow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/FourierAnalysis/code/CentralLimitTheorem.lean)
-/
@[path]
lemma expTaylorRemainder_le_rpow
  {x : ℝ}
  {α : ℝ}
-- given
  (hα1 : 0 < α)
  (hα2 : α < 1) :
-- imply
  ‖expTaylorRemainder x‖ ≤ 4 * := by
-- proof
  calc ‖expTaylorRemainder x‖
    ≤ 4 * min (|x| ^ 2) (|x| ^ 3) := expTaylorRemainder_le_min x
    _ ≤ 4 * |x| ^ (2 + α) := by
      gcongr
      exact min_pow_le_rpow x α hα1 hα2
section CLT
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']

end CentralLimitTheorem

namespace CentralLimitTheorem

/--
[memLp_two_of_higher_moment](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/FourierAnalysis/code/CentralLimitTheorem.lean)
-/
@[path]
lemma memLp_two_of_higher_moment
  [MeasurableSpace Ω]
  [MeasurableSpace Ω']
  {X : Ω → ℝ}
  {α : ℝ}
-- given
  (hα : 0 < α)
  (hLp : MemLp X (ENNReal.ofReal (2 + α)) P) :
-- imply
  MemLp X 2 P := by
-- proof
  apply hLp.mono_exponent
  rw [show (2 : ENNReal) = ENNReal.ofReal 2 from by norm_num]
  exact ENNReal.ofReal_le_ofReal (by linarith)

end CentralLimitTheorem

namespace CentralLimitTheorem

/--
[central_limit_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/FourierAnalysis/code/CentralLimitTheorem.lean)
-/
@[path]
lemma central_limit_theorem
  [MeasurableSpace Ω]
  [MeasurableSpace Ω']
  {X : ℕ → Ω → ℝ}
  {Y : Ω' → ℝ}
  {α : ℝ}
-- given
  (hα : 0 < α)
  (hLp : MemLp (X 0) (ENNReal.ofReal (2 + α)) P)
  (hindep : iIndepFun X P)
  (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
  (hY : HasLaw Y (gaussianReal 0 Var[X 0; P].toNNReal) P') :
-- imply
  TendstoInDistribution (fun (n : ℕ) ω ↦ (√↑n)⁻¹ * (∑ k ∈ Finset.range n, X k ω - ↑n * P[X 0])) atTop Y (fun _ ↦ P) P' := by
-- proof
  exact tendstoInDistribution_inv_sqrt_mul_sum_sub hY
    (memLp_two_of_higher_moment hα hLp) hindep hident

end CentralLimitTheorem


-- created on 2026-10-23
