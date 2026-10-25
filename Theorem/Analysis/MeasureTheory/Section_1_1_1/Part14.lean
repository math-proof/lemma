import Def.Analysis.MeasureTheory.Notation.Part2
import Theorem.Analysis.Section_9_1.Part3
import Def.Analysis.MeasureTheory.Section_1_1_1.Part5
open BoundedInterval

open Pointwise


/-- Helper lemma for Lemma 1.1.2(ii): The set of lattice points in a box is finite. -/
theorem Box.sample_finite {d:ℕ} (B: Box d) {N:ℕ} (hN: N ≠ 0):
  Finite ↥(B.toSet ∩ (Set.range (fun (n:Fin d → ℤ) ↦ .toLp 2 (fun i ↦ (N:ℝ)⁻¹*(n i))))) := by
    rw [Equiv.finite_iff (B.sample_congr N)]
    apply @Pi.finite _ _ _ (fun i ↦ (B.side i).sample_finite hN)

/-- Helper lemma for Lemma 1.1.2(ii): Box volume equals the limit of lattice point counts scaled by N^(-d). -/
theorem Box.vol_eq {d:ℕ} (B: Box d):
  Filter.atTop.Tendsto (fun N:ℕ ↦ (N:ℝ)^(-d:ℝ) * Nat.card ↥(B.toSet ∩ (Set.range (fun (n:Fin d → ℤ) ↦ .toLp 2 (fun i ↦ (N:ℝ)⁻¹*(n i))))))
  (nhds |B|ᵥ) := by
  simp [Box.volume]
  have : ∀ i ∈ Finset.univ, Filter.atTop.Tendsto (fun N:ℕ ↦ (N:ℝ)⁻¹ * Nat.card ↥((B.side i).toSet ∩ Set.range ((fun n:ℤ ↦ (N:ℝ)⁻¹*n)))) (nhds |B.side i|ₗ) := fun i _ ↦ (B.side i).length_eq
  convert tendsto_finset_prod Finset.univ this with N
  simp [Finset.prod_mul_distrib]; left
  norm_cast; simp_rw [←Nat.card_coe_set_eq, ←Nat.card_pi]
  apply Nat.card_congr (B.sample_congr N)

/-- Lemma 1.1.2(ii), helper lemma: Sum of volumes equals limit of lattice counts over a disjoint union. -/
theorem Box.sum_vol_eq {d:ℕ} {T: Finset (Box d)}
 (hT: (T : Set (Box d)).PairwiseDisjoint Box.toSet) :
  Filter.atTop.Tendsto (fun N:ℕ ↦ (N:ℝ)^(-d:ℝ) * Nat.card ↥((⋃ B ∈ T, B.toSet) ∩ (Set.range (fun (n:Fin d → ℤ) ↦ .toLp 2 (fun i ↦ (N:ℝ)⁻¹*(n i))))))
  (nhds (∑ B ∈ T, |B|ᵥ)) := by
  apply (tendsto_finset_sum T (fun B _ ↦ B.vol_eq)).congr'
  rw [Filter.EventuallyEq, Filter.eventually_atTop]; use 1; intro N hN
  symm; convert Finset.mul_sum _ _ _
  convert Nat.cast_sum _ _
  rw [←Finset.sum_coe_sort, ←@Nat.card_sigma _ _ _ ?_]
  . exact Nat.card_congr {
      toFun x := by
        obtain ⟨ x, hx ⟩ := x
        simp at hx
        have hB := hx.1.choose_spec
        refine ⟨ ⟨ hx.1.choose, hB.1 ⟩, ⟨ x, ?_⟩ ⟩
        simp_all
      invFun x := by
        obtain ⟨ ⟨ B, hB ⟩, ⟨ x, hx ⟩ ⟩ := x
        refine ⟨ x, ?_ ⟩
        simp_all; aesop
      left_inv x := by grind
      right_inv x := by
        obtain ⟨ ⟨ B, hB ⟩, ⟨ x, hxB⟩ ⟩ := x
        simp at hxB
        have : ∃ B ∈ T, x ∈ B.toSet := by use B; tauto
        have h : this.choose = B := by
          have h := this.choose_spec
          apply hT.elim h.1 hB
          rw [Set.not_disjoint_iff]; grind
        subst h; rfl
    }
  intro ⟨ B, _ ⟩; convert B.sample_finite ?_
  omega

/-- Lemma 1.1.2(ii): Two disjoint partitions of the same set have equal sums of volumes. -/
theorem Box.measure_uniq {d:ℕ} {T₁ T₂: Finset (Box d)}
 (hT₁: (T₁ : Set (Box d)).PairwiseDisjoint Box.toSet)
 (hT₂: (T₂ : Set (Box d)).PairwiseDisjoint Box.toSet)
 (heq: ⋃ B ∈ T₁, B.toSet = ⋃ B ∈ T₂, B.toSet) :
 ∑ B ∈ T₁, |B|ᵥ = ∑ B ∈ T₂, |B|ᵥ := by
  apply tendsto_nhds_unique _ (Box.sum_vol_eq hT₂)
  rw [←heq]
  exact Box.sum_vol_eq hT₁

