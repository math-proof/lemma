import Def.Analysis.MeasureTheory.Section_1_2_0.Part2
import Theorem.Analysis.Misc.RealERealENNReal
import Theorem.Analysis.Misc.Combinatorics
import Def.Analysis.MeasureTheory.Section_1_2_1.Part9
open BoundedInterval

/-!
# Introduction to Measure Theory, Section 1.2.1: Properties of Lebesgue outer measure

A companion to (the introduction to) Section 1.2.1 of the book "An introduction to Measure Theory".

-/


namespace Remark_1_2_8

-- lemma radius_pos (ε : ℝ) (hε : 0 < ε) (n : ℕ) : 0 < radius ε n := by
  -- unfold radius
  -- apply div_pos hε
  -- exact pow_pos (by norm_num : (0:ℝ) < 2) (n+1)

/-- U\_real is contained in (-ε, 1+ε) -/
lemma U_real_subset (ε : ℝ) (hε : 0 < ε) : U_real ε ⊆ Set.Ioo (-ε) (1 + ε) := by
  intro x hx
  simp only [U_real, Set.mem_iUnion] at hx
  obtain ⟨n, hn⟩ := hx
  simp only [Set.mem_Ioo] at hn ⊢
  have hq := q_in_unit_interval n
  have hr : radius ε n ≤ ε := by
    unfold radius
    apply div_le_self (le_of_lt hε)
    calc (1:ℝ) ≤ 2^1 := by norm_num
      _ ≤ 2^(n+1) := by
        apply pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2)
        omega
  constructor
  · calc -ε ≤ 0 - ε := by linarith
      _ ≤ q n - ε := by linarith [hq.1]
      _ ≤ q n - radius ε n := by linarith
      _ < x := hn.1
  · calc x < q n + radius ε n := hn.2
      _ ≤ q n + ε := by linarith
      _ ≤ 1 + ε := by linarith [hq.2]

/-- U is bounded -/
lemma U_isBounded (ε : ℝ) (hε : 0 < ε) : Bornology.IsBounded (U ε) := by
  have h_subset : U ε ⊆ EuclideanSpace'.equiv_Real ⁻¹' Set.Ioo (-ε) (1 + ε) := by
    apply Set.preimage_mono
    exact U_real_subset ε hε
  apply Bornology.IsBounded.subset _ h_subset
  rw [Metric.isBounded_iff_subset_closedBall 0]
  use max (|(-ε)|) (|1 + ε|) + 1
  intro x hx
  simp only [Set.mem_preimage, Set.mem_Ioo] at hx
  rw [Metric.mem_closedBall, dist_zero_right]
  rw [EuclideanSpace'.norm_eq]
  have hsum : (∑ i : Fin 1, x i ^ 2) = x ⟨0, by omega⟩ ^ 2 := Fin.sum_univ_one _
  rw [hsum, Real.sqrt_sq_eq_abs]
  have h1 : EuclideanSpace'.equiv_Real x = x ⟨0, by omega⟩ := rfl
  have hx' : -ε < x ⟨0, by omega⟩ ∧ x ⟨0, by omega⟩ < 1 + ε := by
    rw [← h1]; exact hx
  have h_bd : |x ⟨0, by omega⟩| ≤ max (|-ε|) (|1 + ε|) := by
    apply abs_le_max_abs_abs <;> linarith [hx'.1, hx'.2]
  linarith

/-- Bound on each component interval's Lebesgue measure -/
lemma component_lebesgue_le (ε : ℝ) (hε : 0 < ε) (n : ℕ) :
    Lebesgue_outer_measure (EuclideanSpace'.equiv_Real ⁻¹' Set.Ioo (q n - ε / 2^(n+1)) (q n + ε / 2^(n+1)))
    ≤ ((2 * ε / 2^(n+1) : ℝ) : EReal) := by
  have h_rad_pos : 0 < ε / 2^(n+1) := div_pos hε (pow_pos (by norm_num : (0:ℝ) < 2) (n+1))
  have h_lt : q n - ε / 2^(n+1) < q n + ε / 2^(n+1) := by linarith
  have h_length : (q n + ε / 2^(n+1)) - (q n - ε / 2^(n+1)) = 2 * ε / 2^(n+1) := by ring
  have h1 := Lebesgue_outer_measure.of_Ioo_le (q n - ε / 2^(n+1)) (q n + ε / 2^(n+1)) h_lt
  simp only [h_length] at h1
  exact h1

/-- Closure of U\_real contains \[0,1\] (density of rationals) -/
lemma U_real_closure_contains_unit_interval (ε : ℝ) (hε : 0 < ε) :
    Set.Icc 0 1 ⊆ closure (U_real ε) := by
  intro x hx
  rw [mem_closure_iff_nhds]
  intro t ht
  -- t is a neighborhood of x, so it contains a ball around x
  rw [Metric.mem_nhds_iff] at ht
  obtain ⟨δ, hδ_pos, hδ_sub⟩ := ht
  -- Find a rational in [0,1] close to x
  have h_rat_exists : ∃ r : ℚ, (r:ℝ) ∈ Set.Icc (0:ℝ) 1 ∧ |(r:ℝ) - x| < δ := by
    by_cases h : x < δ
    · use 0
      constructor
      · simp only [Rat.cast_zero, Set.mem_Icc, le_refl, zero_le_one, and_self]
      · rw [Rat.cast_zero, zero_sub, abs_neg, abs_of_nonneg hx.1]
        exact h
    · push_neg at h
      obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (sub_lt_self x hδ_pos)
      use r
      constructor
      · constructor
        · have : (0:ℝ) ≤ x - δ := by linarith
          linarith
        · linarith [hx.2]
      · rw [abs_sub_comm, abs_sub_lt_iff]
        constructor <;> linarith
  obtain ⟨r, hr_in, hr_close⟩ := h_rat_exists
  -- r is in Set.range of Rat.cast
  have hr_range : (r:ℝ) ∈ Set.range (fun s:ℚ ↦ (s:ℝ)) := ⟨r, rfl⟩
  -- So there exists n with q n = r
  have hr_inter : (r:ℝ) ∈ Set.Icc (0:ℝ) 1 ∩ Set.range (fun s:ℚ ↦ (s:ℝ)) := ⟨hr_in, hr_range⟩
  obtain ⟨n, hn⟩ := q_surj r hr_inter
  -- q n = r, and q n is in U_real (in the interval around itself)
  have hqn_in_U : q n ∈ U_real ε := by
    simp only [U_real, Set.mem_iUnion, Set.mem_Ioo]
    use n
    constructor
    · have : 0 < ε / 2^(n+1) := div_pos hε (pow_pos (by norm_num : (0:ℝ) < 2) (n+1))
      linarith
    · have : 0 < ε / 2^(n+1) := div_pos hε (pow_pos (by norm_num : (0:ℝ) < 2) (n+1))
      linarith
  -- q n is close to x (since q n = r)
  have hqn_in_ball : q n ∈ Metric.ball x δ := by
    rw [Metric.mem_ball, dist_comm]
    calc dist x (q n) = |x - q n| := Real.dist_eq x (q n)
      _ = |x - r| := by rw [hn]
      _ = |r - x| := abs_sub_comm x r
      _ < δ := hr_close
  -- So q n is in t
  have hqn_in_t : q n ∈ t := hδ_sub hqn_in_ball
  exact ⟨q n, hqn_in_t, hqn_in_U⟩

end Remark_1_2_8
