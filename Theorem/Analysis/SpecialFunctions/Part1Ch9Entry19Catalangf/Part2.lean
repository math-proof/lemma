/-
Author: @akiezun, Avocado
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
public import Mathlib.Analysis.SpecialFunctions.Integrals.LogTrigonometric
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.Filter.Basic
public import Mathlib.RingTheory.Binomial
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Topology.Basic
public import Def.Analysis.SpecialFunctions.Part1Ch9Entry19Catalangf.Part2

/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

public section


section

namespace Ramanujan.Part1Ch9

namespace Entry19Catalangf

open scoped Topology

open Filter

noncomputable section

theorem central_split_aux (x : ℝ) (k : ℕ) : chapter9Entry19CentralTerm x k =
    chap9S (Real.cos x) k + chap9S (Real.sin x) k := by
  unfold chapter9Entry19CentralTerm chap9S
  rw [mul_add, add_div]

theorem summable_chap9S_aux {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    Summable (chap9S u) := by
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) summable_two_div_succ_sq
  · unfold chap9S
    apply div_nonneg
    · apply mul_nonneg (Nat.cast_nonneg _)
      exact pow_nonneg hu0 _
    · apply mul_nonneg
      · apply pow_nonneg; norm_num
      · apply pow_nonneg; exact Nat.cast_nonneg _
  · have hchoose : ((Nat.choose (2 * k) k : ℕ) : ℝ) ≤ (2 : ℝ) ^ (2 * k) := by
      have h := Nat.choose_le_two_pow (2 * k) k
      have h2 : ((Nat.choose (2 * k) k : ℕ) : ℝ) ≤ ((((2 ^ (2 * k) : ℕ))) : ℝ) :=
        Nat.cast_le.mpr h
      rwa [Nat.cast_pow, Nat.cast_two] at h2
    have hP : (0 : ℝ) < (2 : ℝ) ^ (2 * k) := by positivity
    have hD := Dpos_aux k
    have hcP : ((Nat.choose (2 * k) k : ℕ) : ℝ) / (2 : ℝ) ^ (2 * k) ≤ 1 :=
      div_le_one_of_le₀ hchoose (le_of_lt hP)
    have hS2 : u ^ (2 * k + 1) ≤ 2 := by
      have h1 : u ^ (2 * k + 1) ≤ 1 := pow_le_one₀ hu0 hu1
      linarith
    have hSD : u ^ (2 * k + 1) / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) ≤
        2 / ((((k + 1 : ℕ)) : ℝ) ^ 2) := by
      have he := sq_succ_le_aux k
      have hepos : (0 : ℝ) < ((((k + 1 : ℕ)) : ℝ) ^ 2) := by
        apply pow_pos
        apply Nat.cast_pos.mpr
        omega
      have step1 : u ^ (2 * k + 1) / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) ≤
          2 / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) :=
        div_le_div_of_nonneg_right hS2 (le_of_lt hD)
      have step2 : (2 : ℝ) / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) ≤
          2 / ((((k + 1 : ℕ)) : ℝ) ^ 2) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
        rw [← one_div, ← one_div]
        exact one_div_le_one_div_of_le hepos he
      exact le_trans step1 step2
    have hSDnn : (0 : ℝ) ≤ u ^ (2 * k + 1) / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) :=
      div_nonneg (pow_nonneg hu0 _) (le_of_lt hD)
    have hmul : (((Nat.choose (2 * k) k : ℕ) : ℝ) / (2 : ℝ) ^ (2 * k)) *
        (u ^ (2 * k + 1) / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)) ≤
        2 / ((((k + 1 : ℕ)) : ℝ) ^ 2) := by
      have h := mul_le_mul hcP hSD hSDnn zero_le_one
      rwa [one_mul] at h
    unfold chap9S
    rw [← div_mul_div_comm]
    exact hmul

theorem tsum_central_split_aux {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ Real.pi / 4) :
    (∑' k : ℕ, chapter9Entry19CentralTerm x k) =
      (∑' k : ℕ, chap9S (Real.cos x) k) + ∑' k : ℕ, chap9S (Real.sin x) k := by
  have hcos := cos_pos_aux hx0 hx
  have hsin_nn := sin_nonneg_aux hx0 hx
  have h1 := summable_chap9S_aux (le_of_lt hcos) (Real.cos_le_one x)
  have h2 := summable_chap9S_aux hsin_nn (Real.sin_le_one x)
  simp only [central_split_aux]
  exact Summable.tsum_add h1 h2

theorem chap9S_zero_aux : (∑' k : ℕ, chap9S 0 k) = 0 := by
  have h : (fun k : ℕ => chap9S 0 k) = fun _ => (0 : ℝ) := by
    funext k
    unfold chap9S
    rw [zero_pow (by omega : 2 * k + 1 ≠ 0), mul_zero, zero_div]
  rw [h]
  exact tsum_zero

theorem chap9T_zero_aux : (∑' k : ℕ, chap9T 0 k) = 0 := by
  have h : (fun k : ℕ => chap9T 0 k) = fun _ => (0 : ℝ) := by
    funext k
    unfold chap9T
    rw [zero_pow (by omega : 2 * k + 1 ≠ 0), mul_zero, zero_div]
  rw [h]
  exact tsum_zero

theorem continuousOn_chap9S_tsum_aux :
    ContinuousOn (fun u : ℝ => ∑' k : ℕ, chap9S u k) (Set.Icc (-1) 1) := by
  refine continuousOn_tsum (fun k => ?_) summable_two_div_succ_sq (fun k u hu => ?_)
  · unfold chap9S
    apply ContinuousOn.div
    · exact ContinuousOn.mul continuousOn_const (ContinuousOn.pow continuousOn_id _)
    · exact continuousOn_const
    · intro v _
      apply ne_of_gt
      apply mul_pos (by positivity)
      exact Dpos_aux k
  · rw [Set.mem_Icc] at hu
    have habs : |u| ≤ 1 := abs_le.mpr hu
    have hchoose : ((Nat.choose (2 * k) k : ℕ) : ℝ) ≤ (2 : ℝ) ^ (2 * k) := by
      have h := Nat.choose_le_two_pow (2 * k) k
      have h2 : ((Nat.choose (2 * k) k : ℕ) : ℝ) ≤ ((((2 ^ (2 * k) : ℕ))) : ℝ) :=
        Nat.cast_le.mpr h
      rwa [Nat.cast_pow, Nat.cast_two] at h2
    have hP : (0 : ℝ) < (2 : ℝ) ^ (2 * k) := by positivity
    have hD := Dpos_aux k
    have hPDnn : (0 : ℝ) ≤ (2 : ℝ) ^ (2 * k) * ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) :=
      mul_nonneg (le_of_lt hP) (le_of_lt hD)
    have hcP : ((Nat.choose (2 * k) k : ℕ) : ℝ) / (2 : ℝ) ^ (2 * k) ≤ 1 :=
      div_le_one_of_le₀ hchoose (le_of_lt hP)
    have he := sq_succ_le_aux k
    have hepos : (0 : ℝ) < ((((k + 1 : ℕ)) : ℝ) ^ 2) := by
      apply pow_pos
      apply Nat.cast_pos.mpr
      omega
    have hpow : |u| ^ (2 * k + 1) ≤ 1 :=
      pow_le_one₀ (abs_nonneg u) habs
    have hSD : |u| ^ (2 * k + 1) / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) ≤
        2 / ((((k + 1 : ℕ)) : ℝ) ^ 2) := by
      have step1 : |u| ^ (2 * k + 1) / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) ≤
          1 / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) :=
        div_le_div_of_nonneg_right hpow (le_of_lt hD)
      have hinv : (1 : ℝ) / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) ≤
          1 / ((((k + 1 : ℕ)) : ℝ) ^ 2) :=
        one_div_le_one_div_of_le hepos he
      have h12 : (1 : ℝ) / ((((k + 1 : ℕ)) : ℝ) ^ 2) ≤
          2 / ((((k + 1 : ℕ)) : ℝ) ^ 2) :=
        div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) (le_of_lt hepos)
      exact le_trans step1 (le_trans hinv h12)
    have hSDnn : (0 : ℝ) ≤ |u| ^ (2 * k + 1) / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) :=
      div_nonneg (pow_nonneg (abs_nonneg u) _) (le_of_lt hD)
    have hmul : (((Nat.choose (2 * k) k : ℕ) : ℝ) / (2 : ℝ) ^ (2 * k)) *
        (|u| ^ (2 * k + 1) / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)) ≤
        2 / ((((k + 1 : ℕ)) : ℝ) ^ 2) := by
      have h := mul_le_mul hcP hSD hSDnn zero_le_one
      rwa [one_mul] at h
    have hnorm : ‖chap9S u k‖ =
        (((Nat.choose (2 * k) k : ℕ) : ℝ) / (2 : ℝ) ^ (2 * k)) *
          (|u| ^ (2 * k + 1) / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)) := by
      unfold chap9S
      rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_pow,
        abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg hPDnn,
        ← div_mul_div_comm]
    rw [hnorm]
    exact hmul

theorem continuousOn_chap9T_tsum_aux :
    ContinuousOn (fun v : ℝ => ∑' k : ℕ, chap9T v k) (Set.Icc (-1) 1) := by
  refine continuousOn_tsum (fun k => ?_) summable_two_div_succ_sq (fun k v hv => ?_)
  · unfold chap9T
    apply ContinuousOn.div
    · exact ContinuousOn.mul continuousOn_const (ContinuousOn.pow continuousOn_id _)
    · exact continuousOn_const
    · intro w _
      apply ne_of_gt
      exact Dpos_aux k
  · rw [Set.mem_Icc] at hv
    have habs : |v| ≤ 1 := abs_le.mpr hv
    have hD := Dpos_aux k
    have he := sq_succ_le_aux k
    have hepos : (0 : ℝ) < ((((k + 1 : ℕ)) : ℝ) ^ 2) := by
      apply pow_pos
      apply Nat.cast_pos.mpr
      omega
    have hpow : |v| ^ (2 * k + 1) ≤ 1 :=
      pow_le_one₀ (abs_nonneg v) habs
    have hle : |v| ^ (2 * k + 1) / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) ≤
        2 / ((((k + 1 : ℕ)) : ℝ) ^ 2) := by
      have step1 : |v| ^ (2 * k + 1) / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) ≤
          1 / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) :=
        div_le_div_of_nonneg_right hpow (le_of_lt hD)
      have hinv : (1 : ℝ) / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) ≤
          1 / ((((k + 1 : ℕ)) : ℝ) ^ 2) :=
        one_div_le_one_div_of_le hepos he
      have h12 : (1 : ℝ) / ((((k + 1 : ℕ)) : ℝ) ^ 2) ≤
          2 / ((((k + 1 : ℕ)) : ℝ) ^ 2) :=
        div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) (le_of_lt hepos)
      exact le_trans step1 (le_trans hinv h12)
    have hnorm : ‖chap9T v k‖ =
        |v| ^ (2 * k + 1) / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) := by
      unfold chap9T
      rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs]
      rw [abs_mul, abs_pow, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_pos hD]
    rw [hnorm]
    exact hle

theorem tan_at_zero_aux : (∑' k : ℕ, chapter9Entry19TanTerm 0 k) = 0 := by
  have h : (fun k : ℕ => chapter9Entry19TanTerm 0 k) = fun _ => (0 : ℝ) := by
    funext k
    unfold chapter9Entry19TanTerm
    rw [Real.tan_zero, zero_pow (by omega : 2 * k + 1 ≠ 0), mul_zero, zero_div]
  rw [h]
  exact tsum_zero

theorem log_two_cos_zero_aux : Real.log (2 * Real.cos 0) = Real.log 2 := by
  rw [Real.cos_zero, mul_one]

end
end Entry19Catalangf
end Ramanujan.Part1Ch9
end
