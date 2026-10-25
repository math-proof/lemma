import Def.Analysis.MeasureTheory.Section_1_2_0.Part2
import Theorem.Analysis.Misc.RealERealENNReal
import Theorem.Analysis.Misc.Combinatorics
import Abbrev.Analysis.MeasureTheory.Section_1_2_1
open BoundedInterval

/-!
# Introduction to Measure Theory, Section 1.2.1: Properties of Lebesgue outer measure

A companion to (the introduction to) Section 1.2.1 of the book "An introduction to Measure Theory".

-/


namespace Remark_1_2_8

/-- Unit interval as the preimage of \[0,1\] equals unit box -/
lemma unit_interval_eq_box : EuclideanSpace'.equiv_Real ⁻¹' Set.Icc 0 1 = unit_box_1D.toSet :=
  preimage_Icc_eq_box 0 1

/-- Volume of unit box is 1 -/
lemma unit_box_volume : |unit_box_1D|ᵥ = 1 := by
  unfold unit_box_1D unit_interval Box.volume BoundedInterval.length
  norm_num

/-- Jordan outer measure of unit box is 1 -/
lemma Jordan_outer_unit_box : Jordan_outer_measure unit_box_1D.toSet = 1 := by
  have h_elem := IsElementary.box unit_box_1D
  have h_jm := h_elem.jordanMeasurable
  rw [← h_jm.eq_outer]
  rw [JordanMeasurable.mes_of_elementary h_elem]
  rw [IsElementary.measure_of_box unit_box_1D]
  exact unit_box_volume

/-- Closure of U contains the preimage of \[0,1\] -/
lemma U_closure_contains_unit_box (ε : ℝ) (hε : 0 < ε) :
    unit_box_1D.toSet ⊆ closure (U ε) := by
  -- Key insight: For a homeomorphism f, closure(f⁻¹(S)) = f⁻¹(closure(S))
  -- Since U ε = equiv_Real⁻¹(U_real ε) and equiv_Real is a homeomorphism:
  -- closure(U ε) = equiv_Real⁻¹(closure(U_real ε)) ⊇ equiv_Real⁻¹([0,1]) = unit_box_1D
  have h_closure_real := U_real_closure_contains_unit_interval ε hε
  rw [← unit_interval_eq_box]
  intro x hx
  rw [Set.mem_preimage] at hx
  have hx_in_closure : EuclideanSpace'.equiv_Real x ∈ closure (U_real ε) :=
    h_closure_real hx
  rw [mem_closure_iff_nhds] at hx_in_closure ⊢
  intro t ht
  rw [Metric.mem_nhds_iff] at ht
  obtain ⟨δ, hδ_pos, hδ_sub⟩ := ht
  have h_ball_nhd : Metric.ball (EuclideanSpace'.equiv_Real x) δ ∈ nhds (EuclideanSpace'.equiv_Real x) :=
    Metric.ball_mem_nhds _ hδ_pos
  obtain ⟨y, hy_ball, hy_U⟩ := hx_in_closure _ h_ball_nhd
  use EuclideanSpace'.equiv_Real.symm y
  constructor
  · apply hδ_sub
    rw [Metric.mem_ball, EuclideanSpace'_dist_eq_Real_dist, Equiv.apply_symm_apply]
    exact hy_ball
  · simp only [U, Set.mem_preimage, Equiv.apply_symm_apply]
    exact hy_U

/-- Jordan outer measure of U ≥ 1.
    Proof uses: density of ℚ → closure(U) ⊇ \[0,1\] → Jordan\_outer(U) ≥ Jordan\_outer(\[0,1\]) = 1. -/
lemma U_jordan_outer_ge (ε : ℝ) (hε : 0 < ε) :
    Jordan_outer_measure (U ε) ≥ 1 := by
  -- By JordanMeasurable.outer_measure_of_closure, Jordan_outer(closure U) = Jordan_outer(U)
  have h_closure_eq := JordanMeasurable.outer_measure_of_closure (U_isBounded ε hε)
  -- closure(U) ⊇ unit_box, so by monotonicity:
  have h_closure_contains := U_closure_contains_unit_box ε hε
  have h_unit_bound : Jordan_outer_measure unit_box_1D.toSet ≤ Jordan_outer_measure (closure (U ε)) := by
    apply Jordan_outer_measure_mono h_closure_contains
    exact Bornology.IsBounded.closure (U_isBounded ε hε)
  calc 1 = Jordan_outer_measure unit_box_1D.toSet := Jordan_outer_unit_box.symm
    _ ≤ Jordan_outer_measure (closure (U ε)) := h_unit_bound
    _ = Jordan_outer_measure (U ε) := h_closure_eq

/-- Lebesgue outer measure of U ≤ 2ε (countable subadditivity).
    U = ⋃\_n (q\_n - ε/2^\{n+1\}, q\_n + ε/2^\{n+1\}), each interval has length 2ε/2^\{n+1\},
    and ∑ 2ε/2^\{n+1\} = 2ε.

    Proof structure:
    1. Express U as countable union: U = ⋃\_n E\_n
    2. By countable subadditivity (union\_le): m\*(U) ≤ ∑' m\*(E\_n)
    3. Each component bounded: m\*(E\_n) ≤ 2ε/2^\{n+1\} (component\_lebesgue\_le)
    4. Geometric sum: ∑' 2ε/2^\{n+1\} = 2ε (tsum\_interval\_lengths)
    5. {name}`EReal` tsum comparison: ∑' m\*(E\_n) ≤ ∑' (2ε/2^\{n+1\}) = 2ε -/
lemma U_lebesgue_le (ε : ℝ) (hε : 0 < ε) :
    Lebesgue_outer_measure (U ε) ≤ ((2 * ε : ℝ) : EReal) := by
  -- U = ⋃_n (component intervals in EuclideanSpace' 1)
  let E : ℕ → Set (EuclideanSpace' 1) := fun n =>
    EuclideanSpace'.equiv_Real ⁻¹' Set.Ioo (q n - ε / 2^(n+1)) (q n + ε / 2^(n+1))
  -- U ε = ⋃ n, E n
  have h_U_eq : U ε = ⋃ n, E n := by
    ext x
    simp only [U, U_real, Set.mem_preimage, Set.mem_iUnion, E]
  -- By countable subadditivity: m*(U) ≤ ∑' n, m*(E n)
  have h_subadditive := Lebesgue_outer_measure.union_le E
  -- Each component has m*(E n) ≤ 2ε/2^{n+1}
  have h_component_bound : ∀ n, Lebesgue_outer_measure (E n) ≤ ((2 * ε / 2^(n+1) : ℝ) : EReal) :=
    fun n => component_lebesgue_le ε hε n
  -- Sum bound: ∑' n, m*(E n) ≤ 2ε
  have h_sum_bound : ∑' n, Lebesgue_outer_measure (E n) ≤ ((2 * ε : ℝ) : EReal) := by
    have h_g_nonneg : ∀ n, 0 ≤ 2 * ε / 2^(n+1) := by
      intro n
      apply div_nonneg (by linarith : 0 ≤ 2 * ε)
      exact pow_nonneg (by norm_num : (0:ℝ) ≤ 2) _
    have h_tsum_eq := tsum_interval_lengths ε hε
    rw [← h_tsum_eq]
    -- Lebesgue outer measure is non-negative (sInf of sums of box volumes ≥ 0)
    have h_f_nonneg : ∀ n, 0 ≤ Lebesgue_outer_measure (E n) := fun n =>
      Lebesgue_outer_measure.nonneg (E n)
    -- Summability of the geometric series
    have h_summable : Summable (fun n => 2 * ε / 2^(n+1)) := tsum_interval_summable ε
    -- Use coe_tsum lemma: ↑(∑' g) = ∑' (↑g)
    rw [EReal.coe_tsum_of_nonneg h_g_nonneg h_summable]
    -- Apply the helper lemma for pointwise comparison
    exact EReal.tsum_le_coe_tsum_of_forall_le h_f_nonneg h_g_nonneg h_summable h_component_bound
  calc Lebesgue_outer_measure (U ε) = Lebesgue_outer_measure (⋃ n, E n) := by rw [h_U_eq]
    _ ≤ ∑' n, Lebesgue_outer_measure (E n) := h_subadditive
    _ ≤ ((2 * ε : ℝ) : EReal) := h_sum_bound

end Remark_1_2_8
