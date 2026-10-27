import Mathlib
import Initialize.Tactic.Attr.Basic
open MeasureTheory


/--
[MeasureTheory_Measure_measure_coe_eq_relIndex_mul_of_le_of_isAddLeftInvariant](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_MeasureTheory_Measure_measure_coe_eq_relIndex_mul_of_le_of_isAddLeftInvariant.lean)
-/
@[path]
private lemma main
  [AddGroup G] [MeasurableSpace G] [MeasurableAdd G]
  {μ : Measure G} [μ.IsAddLeftInvariant]
  {H H' : AddSubgroup G}
-- given
  (hle : H ≤ H')
  (hH : MeasurableSet (H : Set G))
  (hfin : H.relIndex H' ≠ 0) :
-- imply
  μ (H' : Set G) = (H.relIndex H' : ENNReal) * μ (H : Set G) := by
-- proof
  classical
    set K : AddSubgroup H' := H.addSubgroupOf H' with hK
    have : K.FiniteIndex := ⟨hfin⟩
    have : Finite (H' ⧸ K) := AddSubgroup.finite_quotient_of_finiteIndex
    have : Fintype (H' ⧸ K) := Fintype.ofFinite _
    let rep : H' ⧸ K → G := fun c => ((Quotient.out c : H') : G)
    let C : H' ⧸ K → Set G := fun c => (fun x : G => -(rep c) + x) ⁻¹' (H : Set G)
    have hmemC : ∀ (c : H' ⧸ K) (x : G), x ∈ C c ↔ -(rep c) + x ∈ H := fun c x => Iff.rfl
    have hrel : ∀ a b : H', (QuotientAddGroup.mk (s := K) a = QuotientAddGroup.mk b) ↔ -(a : G) + b ∈ H := by
      intro a b
      rw [QuotientAddGroup.eq, hK, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_add, AddSubgroup.coe_neg]
    have hcover : (H' : Set G) = ⋃ c, C c := by
      ext x
      rw [Set.mem_iUnion]
      constructor
      ·
        intro hx
        refine ⟨QuotientAddGroup.mk (s := K) ⟨x, hx⟩, ?_⟩
        rw [hmemC]
        have h := QuotientAddGroup.out_eq' (QuotientAddGroup.mk (s := K) (⟨x, hx⟩ : H'))
        refine (hrel _ _).mp h
      ·
        rintro ⟨c, hc⟩
        rw [hmemC] at hc
        have hg : rep c ∈ H' := ((Quotient.out c : H')).2
        have hx : x = rep c + (-(rep c) + x) := (add_neg_cancel_left (rep c) x).symm
        rw [SetLike.mem_coe, hx]
        exact H'.add_mem hg (hle hc)
    have hdisj : Pairwise (Function.onFun Disjoint C) := by
      intro c₁ c₂ hne
      rw [Function.onFun, Set.disjoint_left]
      intro x h₁ h₂
      apply hne
      rw [hmemC] at h₁ h₂
      have hmem : -(rep c₁) + rep c₂ ∈ H := by
        have : -(rep c₁) + rep c₂ = (-(rep c₁) + x) + -(-(rep c₂) + x) := by
          rw [neg_add_rev, neg_neg, add_assoc, add_neg_cancel_left]
        rw [this]
        exact H.add_mem h₁ (H.neg_mem h₂)
      rw [← QuotientAddGroup.out_eq' c₁, ← QuotientAddGroup.out_eq' c₂]
      exact (hrel _ _).mpr hmem
    have hmeas : ∀ c, MeasurableSet (C c) := fun c => hH.preimage (measurable_const_add _)
    have hμC : ∀ c, μ (C c) = μ (H : Set G) := fun c => measure_preimage_add μ _ _
    rw [hcover, measure_iUnion hdisj hmeas, tsum_fintype, Finset.sum_congr rfl (fun c _ => hμC c), Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    congr 1
    rw [AddSubgroup.relIndex, AddSubgroup.index, ← hK, Nat.card_eq_fintype_card]


-- created on 2026-10-23
