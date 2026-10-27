import Mathlib
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal MeasureTheory ProbabilityTheory


namespace ChernoffBound

/--
[chernoff_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter5/ChernoffBound.lean)
-/
@[path]
lemma chernoff_bound
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {n : ℕ}
  {X : Fin n → Ω → ℝ}
  {a : ℝ}
-- given
  (hn : 0 < n)
  (h_indep : iIndepFun X μ)
  (h_meas : ∀ i, AEMeasurable (X i) μ)
  (h_bdd : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (-1 : ℝ) 1)
  (h_mean : ∀ i, μ[X i] = 0)
  (ha : 0 < a) :
-- imply
  μ.real {ω | a * Real.sqrt n ≤ ∑ i, X i ω} ≤ Real.exp (-a ^ 2 / 2) := by
-- proof
  have h_subG : ∀ i : Fin n, HasSubgaussianMGF (X i) 1 μ := by
    intro i
    have := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (h_meas i) (h_bdd i) (h_mean i)
    convert this using 1
    ext; simp [NNReal.coe_pow, NNReal.coe_div]
    norm_num
  have h_sum : HasSubgaussianMGF (fun ω => ∑ i, X i ω)
    (∑ _i ∈ (Finset.univ : Finset (Fin n)), (1 : ℝ≥0)) μ :=
    HasSubgaussianMGF.sum_of_iIndepFun h_indep (fun i _ => h_subG i)
  have haε : 0 ≤ a * Real.sqrt n := by positivity
  have key := h_sum.measure_ge_le haε
  suffices h_eq : -(a * √↑n) ^ 2 / (2 * ↑(∑ _i ∈ (Finset.univ : Finset (Fin n)), (1 : ℝ≥0)))
    = -a ^ 2 / 2 by
    rwa [h_eq] at key
  have h_sum_val : (∑ _i ∈ (Finset.univ : Finset (Fin n)), (1 : ℝ≥0) : ℝ≥0) = (n : ℝ≥0) := by
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [h_sum_val]
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  simp only [mul_pow, Real.sq_sqrt (le_of_lt hn_pos)]
  rw [show (↑(n : ℝ≥0) : ℝ) = (n : ℝ) from by simp]
  field_simp

end ChernoffBound

namespace ChernoffBound

/--
[chernoff_bound_two_sided](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter5/ChernoffBound.lean)
-/
@[path]
lemma chernoff_bound_two_sided
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {n : ℕ}
  {X : Fin n → Ω → ℝ}
  {a : ℝ}
-- given
  (hn : 0 < n)
  (h_indep : iIndepFun X μ)
  (h_meas : ∀ i, AEMeasurable (X i) μ)
  (h_bdd : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (-1 : ℝ) 1)
  (h_mean : ∀ i, μ[X i] = 0)
  (ha : 0 < a) :
-- imply
  μ.real {ω | a * Real.sqrt n ≤ |∑ i, X i ω|} ≤ 2 * Real.exp (-a ^ 2 / 2) := by
-- proof
  have h_subset : {ω | a * √↑n ≤ |∑ i, X i ω|} ⊆
    {ω | a * √↑n ≤ ∑ i, X i ω} ∪ {ω | a * √↑n ≤ ∑ i, -(X i ω)} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Set.mem_union] at *
    obtain h1 | h1 := le_or_gt (∑ i, X i ω) 0
    · right
      rw [abs_of_nonpos h1] at hω
      rwa [Finset.sum_neg_distrib]
    · left
      rwa [abs_of_pos h1] at hω
  have h_neg_indep : iIndepFun (fun i ω => -(X i ω)) μ :=
    h_indep.comp (fun _ => Neg.neg) (fun _ => measurable_neg)
  have h_neg_meas : ∀ i, AEMeasurable (fun ω => -(X i ω)) μ :=
    fun i => (h_meas i).neg
  have h_neg_bdd : ∀ i, ∀ᵐ ω ∂μ, -(X i ω) ∈ Set.Icc (-1 : ℝ) 1 := by
    intro i
    filter_upwards [h_bdd i] with ω hω
    simp only [Set.mem_Icc] at hω ⊢
    constructor <;> linarith
  have h_neg_mean : ∀ i, μ[fun ω => -(X i ω)] = 0 := by
    intro i; rw [integral_neg, h_mean i, neg_zero]
  have h_upper := chernoff_bound hn h_indep h_meas h_bdd h_mean ha
  have h_lower := chernoff_bound hn h_neg_indep h_neg_meas h_neg_bdd h_neg_mean ha
  calc μ.real {ω | a * √↑n ≤ |∑ i, X i ω|}
    ≤ μ.real ({ω | a * √↑n ≤ ∑ i, X i ω} ∪ {ω | a * √↑n ≤ ∑ i, -(X i ω)}) :=
      measureReal_mono h_subset (measure_ne_top μ _)
    _ ≤ μ.real {ω | a * √↑n ≤ ∑ i, X i ω} + μ.real {ω | a * √↑n ≤ ∑ i, -(X i ω)} :=
      measureReal_union_le _ _
    _ ≤ exp (-a ^ 2 / 2) + exp (-a ^ 2 / 2) := by linarith
    _ = 2 * exp (-a ^ 2 / 2) := by ring

end ChernoffBound


-- created on 2026-10-23
