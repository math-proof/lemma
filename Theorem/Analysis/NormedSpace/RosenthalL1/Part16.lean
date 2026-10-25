/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Nth
import Def.Analysis.NormedSpace.RosenthalL1.Part15
/-!
# Rosenthal's `ℓ¹` theorem

This file proves that every bounded sequence in a real or complex Banach space has either a weakly
Cauchy subsequence or a subsequence with a uniform `ℓ¹` lower bound.
-/


namespace FunctionalAnalysis.RosenthalL1Wanted

theorem rosenthal_assignmentIndices_even (P : Finset ℕ) (n : ℕ) :
    rosenthalAssignmentIndices P (2 * n) =
      if n ∈ P then 3 * n + 1 else 3 * n := by
  have hdiv : 2 * n / 2 = n := by omega
  have hmod : 2 * n % 2 = 0 := by omega
  simp [rosenthalAssignmentIndices, hdiv, hmod]

theorem rosenthal_assignmentIndices_odd (P : Finset ℕ) (n : ℕ) :
    rosenthalAssignmentIndices P (2 * n + 1) =
      if n ∈ P then 3 * n + 2 else 3 * n + 1 := by
  have hdiv : (2 * n + 1) / 2 = n := by omega
  have hmod : (2 * n + 1) % 2 = 1 := by omega
  simp [rosenthalAssignmentIndices, hdiv, hmod]

theorem rosenthal_assignmentIndices_strictMono (P : Finset ℕ) :
    StrictMono (rosenthalAssignmentIndices P) := by
  apply strictMono_nat_of_lt_succ
  intro n
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [rosenthal_assignmentIndices_even, rosenthal_assignmentIndices_odd]
    split <;> omega
  · rw [rosenthal_assignmentIndices_odd,
      show 2 * i + 1 + 1 = 2 * (i + 1) by omega,
      rosenthal_assignmentIndices_even]
    split <;> split <;> omega

theorem rosenthal_cell_pair_assignments
    {K 𝕜 : Type*} [PseudoMetricSpace 𝕜]
    (f : ℕ → K → 𝕜) (delta : ℝ) (u v : 𝕜)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hall : ∀ θ : ℕ → ℕ, StrictMono θ →
      rosenthalPaired (rosenthalCellPair f delta u v) (φ ∘ θ)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Set.range ψ ⊆ Set.range φ ∧
      ∀ P Q : Finset ℕ, Disjoint P Q → ∃ k : K,
        (∀ i ∈ P, dist (f (ψ i) k) u ≤ delta) ∧
          ∀ i ∈ Q, dist (f (ψ i) k) v ≤ delta := by
  classical
  let sparse : ℕ → ℕ := fun n => 3 * n + 1
  have hsparse : StrictMono sparse := by
    apply strictMono_nat_of_lt_succ
    intro n
    dsimp [sparse]
    omega
  refine ⟨φ ∘ sparse, hφ.comp hsparse, Set.range_comp_subset_range sparse φ, ?_⟩
  intro P Q hPQ
  obtain ⟨k, hk⟩ := hall (rosenthalAssignmentIndices P)
    (rosenthal_assignmentIndices_strictMono P)
  refine ⟨k, ?_, ?_⟩
  · intro i hi
    have hpair := (hk i).1
    simpa [rosenthalCellPair, Function.comp_def, sparse,
      rosenthal_assignmentIndices_even, hi] using hpair
  · intro i hi
    have hnot : i ∉ P := by
      intro hip
      exact Finset.disjoint_left.mp hPQ hip hi
    have hpair := (hk i).2
    simpa [rosenthalCellPair, Function.comp_def, sparse,
      rosenthal_assignmentIndices_odd, hnot] using hpair

theorem rosenthal_norm_le_abs_re_add_abs_im
    {𝕜 : Type*} [RCLike 𝕜] (z : 𝕜) :
    ‖z‖ ≤ |RCLike.re z| + |RCLike.im z| := by
  rw [← RCLike.re_add_im z]
  refine (norm_add_le _ _).trans ?_
  rw [RCLike.norm_ofReal, norm_mul, RCLike.norm_ofReal, RCLike.norm_I]
  split <;> simp [abs_nonneg]

theorem rosenthal_exists_large_quadrant
    {𝕜 : Type*} [RCLike 𝕜] (s : Finset ℕ) (z : ℕ → 𝕜) :
    ∃ P : Finset ℕ, P ⊆ s ∧
      (∑ i ∈ s, ‖z i‖) / 4 ≤ ‖∑ i ∈ P, z i‖ := by
  classical
  let rp := s.filter fun i => 0 ≤ RCLike.re (z i)
  let rn := s.filter fun i => ¬0 ≤ RCLike.re (z i)
  let ip := s.filter fun i => 0 ≤ RCLike.im (z i)
  let inn := s.filter fun i => ¬0 ≤ RCLike.im (z i)
  have hrp : (∑ i ∈ rp, |RCLike.re (z i)|) ≤ ‖∑ i ∈ rp, z i‖ := by
    calc
      (∑ i ∈ rp, |RCLike.re (z i)|) = ∑ i ∈ rp, RCLike.re (z i) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact abs_of_nonneg (Finset.mem_filter.mp hi).2
      _ = RCLike.re (∑ i ∈ rp, z i) := by
        symm
        exact map_sum RCLike.re _ _
      _ ≤ ‖∑ i ∈ rp, z i‖ := RCLike.re_le_norm _
  have hrn : (∑ i ∈ rn, |RCLike.re (z i)|) ≤ ‖∑ i ∈ rn, z i‖ := by
    calc
      (∑ i ∈ rn, |RCLike.re (z i)|) = ∑ i ∈ rn, -RCLike.re (z i) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact abs_of_neg (lt_of_not_ge (Finset.mem_filter.mp hi).2)
      _ = -RCLike.re (∑ i ∈ rn, z i) := by
        rw [Finset.sum_neg_distrib]
        congr 1
        exact (map_sum (RCLike.re : 𝕜 →+ ℝ) z rn).symm
      _ ≤ ‖∑ i ∈ rn, z i‖ := by
        simpa only [map_neg, norm_neg] using RCLike.re_le_norm (-(∑ i ∈ rn, z i))
  have hip : (∑ i ∈ ip, |RCLike.im (z i)|) ≤ ‖∑ i ∈ ip, z i‖ := by
    calc
      (∑ i ∈ ip, |RCLike.im (z i)|) = ∑ i ∈ ip, RCLike.im (z i) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact abs_of_nonneg (Finset.mem_filter.mp hi).2
      _ = RCLike.im (∑ i ∈ ip, z i) := by
        symm
        exact map_sum RCLike.im _ _
      _ ≤ ‖∑ i ∈ ip, z i‖ := RCLike.im_le_norm _
  have hinn : (∑ i ∈ inn, |RCLike.im (z i)|) ≤ ‖∑ i ∈ inn, z i‖ := by
    calc
      (∑ i ∈ inn, |RCLike.im (z i)|) = ∑ i ∈ inn, -RCLike.im (z i) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact abs_of_neg (lt_of_not_ge (Finset.mem_filter.mp hi).2)
      _ = -RCLike.im (∑ i ∈ inn, z i) := by
        rw [Finset.sum_neg_distrib]
        congr 1
        exact (map_sum (RCLike.im : 𝕜 →+ ℝ) z inn).symm
      _ ≤ ‖∑ i ∈ inn, z i‖ := by
        simpa only [map_neg, norm_neg] using RCLike.im_le_norm (-(∑ i ∈ inn, z i))
  have hre : (∑ i ∈ s, |RCLike.re (z i)|) ≤
      ‖∑ i ∈ rp, z i‖ + ‖∑ i ∈ rn, z i‖ := by
    rw [← Finset.sum_filter_add_sum_filter_not s
      (fun i => 0 ≤ RCLike.re (z i)) (fun i => |RCLike.re (z i)|)]
    change (∑ i ∈ rp, |RCLike.re (z i)|) + (∑ i ∈ rn, |RCLike.re (z i)|) ≤ _
    exact add_le_add hrp hrn
  have him : (∑ i ∈ s, |RCLike.im (z i)|) ≤
      ‖∑ i ∈ ip, z i‖ + ‖∑ i ∈ inn, z i‖ := by
    rw [← Finset.sum_filter_add_sum_filter_not s
      (fun i => 0 ≤ RCLike.im (z i)) (fun i => |RCLike.im (z i)|)]
    change (∑ i ∈ ip, |RCLike.im (z i)|) + (∑ i ∈ inn, |RCLike.im (z i)|) ≤ _
    exact add_le_add hip hinn
  have htotal : (∑ i ∈ s, ‖z i‖) ≤
      ‖∑ i ∈ rp, z i‖ + ‖∑ i ∈ rn, z i‖ +
        ‖∑ i ∈ ip, z i‖ + ‖∑ i ∈ inn, z i‖ := by
    have hcoord : (∑ i ∈ s, ‖z i‖) ≤
        (∑ i ∈ s, |RCLike.re (z i)|) +
          ∑ i ∈ s, |RCLike.im (z i)| := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun i _ => rosenthal_norm_le_abs_re_add_abs_im (z i)
    linarith
  by_cases h : (∑ i ∈ s, ‖z i‖) / 4 ≤ ‖∑ i ∈ rp, z i‖
  · exact ⟨rp, Finset.filter_subset _ _, h⟩
  by_cases h' : (∑ i ∈ s, ‖z i‖) / 4 ≤ ‖∑ i ∈ rn, z i‖
  · exact ⟨rn, Finset.filter_subset _ _, h'⟩
  by_cases h'' : (∑ i ∈ s, ‖z i‖) / 4 ≤ ‖∑ i ∈ ip, z i‖
  · exact ⟨ip, Finset.filter_subset _ _, h''⟩
  refine ⟨inn, Finset.filter_subset _ _, ?_⟩
  by_contra h'''
  push Not at h h' h'' h'''
  linarith

end FunctionalAnalysis.RosenthalL1Wanted
