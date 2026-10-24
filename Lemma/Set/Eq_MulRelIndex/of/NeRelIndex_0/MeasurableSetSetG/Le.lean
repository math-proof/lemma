import Mathlib
import sympy.Basic
open MeasureTheory


/--
[MeasureTheory_Measure_measure_coe_eq_relIndex_mul_of_le_of_isMulLeftInvariant](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_MeasureTheory_Measure_measure_coe_eq_relIndex_mul_of_le_of_isMulLeftInvariant.lean)
-/
@[path]
private lemma main
  [Group G] [MeasurableSpace G] [MeasurableMul G]
  {μ : Measure G} [μ.IsMulLeftInvariant]
  {H H' : Subgroup G}
-- given
  (hle : H ≤ H')
  (hH : MeasurableSet (H : Set G))
  (hfin : H.relIndex H' ≠ 0) :
-- imply
  μ (H' : Set G) = (H.relIndex H' : ENNReal) * μ (H : Set G) := by
-- proof
  classical
    set K : Subgroup H' := H.subgroupOf H' with hK
    have : K.FiniteIndex := ⟨hfin⟩
    have : Finite (H' ⧸ K) := Subgroup.finite_quotient_of_finiteIndex
    have : Fintype (H' ⧸ K) := Fintype.ofFinite _
    let rep : H' ⧸ K → G := fun c => ((Quotient.out c : H') : G)
    let C : H' ⧸ K → Set G := fun c => (fun x : G => (rep c)⁻¹ * x) ⁻¹' (H : Set G)
    have hmemC : ∀ (c : H' ⧸ K) (x : G), x ∈ C c ↔ (rep c)⁻¹ * x ∈ H := fun c x => Iff.rfl
    have hrel : ∀ a b : H', (QuotientGroup.mk (s := K) a = QuotientGroup.mk b) ↔ (a : G)⁻¹ * b ∈ H := by
      intro a b
      rw [QuotientGroup.eq, hK, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    have hcover : (H' : Set G) = ⋃ c, C c := by
      ext x
      rw [Set.mem_iUnion]
      constructor
      ·
        intro hx
        refine ⟨QuotientGroup.mk (s := K) ⟨x, hx⟩, ?_⟩
        rw [hmemC]
        have h := QuotientGroup.out_eq' (QuotientGroup.mk (s := K) (⟨x, hx⟩ : H'))
        refine (hrel _ _).mp h
      ·
        rintro ⟨c, hc⟩
        rw [hmemC] at hc
        have hg : rep c ∈ H' := ((Quotient.out c : H')).2
        have hx : x = rep c * ((rep c)⁻¹ * x) := by group
        rw [SetLike.mem_coe, hx]
        exact H'.mul_mem hg (hle hc)
    have hdisj : Pairwise (Function.onFun Disjoint C) := by
      intro c₁ c₂ hne
      rw [Function.onFun, Set.disjoint_left]
      intro x h₁ h₂
      apply hne
      rw [hmemC] at h₁ h₂
      have hmem : (rep c₁)⁻¹ * rep c₂ ∈ H := by
        have : (rep c₁)⁻¹ * rep c₂ = ((rep c₁)⁻¹ * x) * ((rep c₂)⁻¹ * x)⁻¹ := by group
        rw [this]
        exact H.mul_mem h₁ (H.inv_mem h₂)
      rw [← QuotientGroup.out_eq' c₁, ← QuotientGroup.out_eq' c₂]
      exact (hrel _ _).mpr hmem
    have hmeas : ∀ c, MeasurableSet (C c) := fun c => hH.preimage (measurable_const_mul _)
    have hμC : ∀ c, μ (C c) = μ (H : Set G) := fun c => measure_preimage_mul μ _ _
    rw [hcover, measure_iUnion hdisj hmeas, tsum_fintype, Finset.sum_congr rfl (fun c _ => hμC c), Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    congr 1
    rw [Subgroup.relIndex, Subgroup.index, ← hK, Nat.card_eq_fintype_card]


-- created on 2026-10-23
