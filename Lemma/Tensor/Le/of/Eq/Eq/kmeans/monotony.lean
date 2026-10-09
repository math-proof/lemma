import Mathlib.Algebra.Order.BigOperators.Group.Finset
import sympy.concrete.expr_with_limits
import Mathlib.Analysis.InnerProductSpace.PiL2
import Lemma.Finset.Eq.of.In.In.Lt.Lt.EqBiUnion.EqSum_Card
open Finset


@[path]
private lemma main
  {M k d : ℕ} [NeZero k]
  {w w' : ℕ → Finset ℕ}
  {x : ℕ → EuclideanSpace ℝ (Fin d)}
-- given
  (h₀ : ∑ i ∈ Finset.range k, (w i).card = M)
  (h₁ : (Finset.range k).biUnion w = Finset.range M)
  (h₂ : ∀ i, w' i = (Finset.range M).filter fun j =>
    ((ArgMin Set.univ (fun i' : Fin k =>
      ‖x j - (((w i').card : ℝ)⁻¹ • ∑ j' ∈ w i', x j')‖) : Fin k) : ℕ) = i) :
-- imply
  ∑ i ∈ Finset.range k, ∑ j ∈ w' i,
      ‖x j - (((w' i).card : ℝ)⁻¹ • ∑ j' ∈ w' i, x j')‖ ^ 2 ≤
    ∑ i ∈ Finset.range k, ∑ j ∈ w i,
      ‖x j - (((w i).card : ℝ)⁻¹ • ∑ j' ∈ w i, x j')‖ ^ 2 := by
-- proof
  have hmean : ∀ (s : Finset ℕ) (c : EuclideanSpace ℝ (Fin d)),
      ∑ j ∈ s, ‖x j - ((s.card : ℝ)⁻¹ • ∑ j' ∈ s, x j')‖ ^ 2 ≤
        ∑ j ∈ s, ‖x j - c‖ ^ 2 := by
    intro s c
    obtain rfl | hs := s.eq_empty_or_nonempty
    · simp
    ·
      set m := (s.card : ℝ)⁻¹ • ∑ j' ∈ s, x j' with hm_def
      have hm : (s.card : ℝ) • m = ∑ j' ∈ s, x j' := by
        rw [hm_def, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hs.card_pos.ne'), one_smul]
      have key : ∀ j,
          ‖x j - c‖ ^ 2 = ‖x j - m‖ ^ 2 + 2 * inner ℝ (x j - m) (m - c) + ‖m - c‖ ^ 2 := fun j => by
        rw [show x j - c = (x j - m) + (m - c) by abel]
        exact norm_add_sq_real _ _
      have hz : ∑ j ∈ s, inner ℝ (x j - m) (m - c) = 0 := by
        rw [← sum_inner, Finset.sum_sub_distrib, Finset.sum_const,
          ← Nat.cast_smul_eq_nsmul ℝ, hm, sub_self, inner_zero_left]
      rw [Finset.sum_congr rfl fun j _ => key j, Finset.sum_add_distrib,
        Finset.sum_add_distrib, ← Finset.mul_sum, hz, mul_zero, add_zero]
      exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hmin : ∀ j (i' : Fin k),
      ‖x j - (((w ((ArgMin Set.univ (fun i' : Fin k =>
        ‖x j - (((w i').card : ℝ)⁻¹ • ∑ j' ∈ w i', x j')‖) : Fin k) : ℕ)).card : ℝ)⁻¹ •
          ∑ j' ∈ w (ArgMin Set.univ (fun i' : Fin k =>
            ‖x j - (((w i').card : ℝ)⁻¹ • ∑ j' ∈ w i', x j')‖) : Fin k), x j')‖ ≤
        ‖x j - (((w i').card : ℝ)⁻¹ • ∑ j' ∈ w i', x j')‖ := by
    intro j i'
    suffices hex : ∃ a : Fin k, a ∈ (Set.univ : Set (Fin k)) ∧ ∀ y : Fin k,
        y ∈ (Set.univ : Set (Fin k)) →
          ‖x j - (((w (a : ℕ)).card : ℝ)⁻¹ • ∑ j' ∈ w (a : ℕ), x j')‖ ≤
            ‖x j - (((w (y : ℕ)).card : ℝ)⁻¹ • ∑ j' ∈ w (y : ℕ), x j')‖ by
      exact (Classical.epsilon_spec hex).2 i' trivial
    obtain ⟨a, _, ha⟩ := Finset.exists_min_image Finset.univ
      (fun i' : Fin k => ‖x j - (((w i').card : ℝ)⁻¹ • ∑ j' ∈ w i', x j')‖)
      Finset.univ_nonempty
    exact ⟨a, trivial, fun y _ => ha y (Finset.mem_univ y)⟩
  obtain ⟨A, hA⟩ : ∃ A : ℕ → Fin k, ∀ j,
      ArgMin Set.univ (fun i' : Fin k =>
        ‖x j - (((w i').card : ℝ)⁻¹ • ∑ j' ∈ w i', x j')‖) = A j :=
    ⟨_, fun _ => rfl⟩
  simp only [hA] at h₂ hmin
  have hdisj : ((Finset.range k : Finset ℕ) : Set ℕ).PairwiseDisjoint w := by
    intro i1 hi1 i2 hi2 hne
    exact Finset.disjoint_left.mpr fun j hj1 hj2 =>
      hne (Eq.of.In.In.Lt.Lt.EqBiUnion.EqSum_Card h₀ h₁
        (Finset.mem_range.mp (Finset.mem_coe.mp hi1))
        (Finset.mem_range.mp (Finset.mem_coe.mp hi2)) hj1 hj2)
  set F : ℕ → ℝ := fun j =>
      ‖x j - (((w (A j : ℕ)).card : ℝ)⁻¹ • ∑ j' ∈ w (A j : ℕ), x j')‖ ^ 2 with hF
  calc _ ≤
      ∑ i ∈ Finset.range k, ∑ j ∈ w' i,
        ‖x j - (((w i).card : ℝ)⁻¹ • ∑ j' ∈ w i, x j')‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => hmean (w' i) _
    _ = ∑ i ∈ Finset.range k,
          ∑ j ∈ (Finset.range M).filter (fun j => (A j : ℕ) = i), F j := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [h₂ i]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [hF]
        simp only [(Finset.mem_filter.mp hj).2]
    _ = ∑ j ∈ Finset.range M, F j :=
        Finset.sum_fiberwise_of_maps_to
          (fun j _ => Finset.mem_range.mpr (A j).isLt) F
    _ = ∑ i ∈ Finset.range k, ∑ j ∈ w i, F j := by
        rw [← h₁, Finset.sum_biUnion hdisj]
    _ ≤ _ := by
        refine Finset.sum_le_sum fun i hi =>
          Finset.sum_le_sum fun j _ => ?_
        exact pow_le_pow_left₀ (norm_nonneg _)
          (hmin j ⟨i, Finset.mem_range.mp hi⟩) 2


-- created on 2026-10-09
