import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet


/--
[weight_gen_fun_prod_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
  [CommSemiring R]
-- given
  {α β : Type*} [DecidableEq α] [DecidableEq β]
  (W₁ : WeightedSet α)
  (W₂ : WeightedSet β)
  (hft₁ : W₁.IsFiniteType)
  (hft₂ : W₂.IsFiniteType) :
-- imply
  (prod W₁ W₂).weightGenFun (R := R) (prod_isFiniteType W₁ W₂ hft₁ hft₂) =
    W₁.weightGenFun hft₁ * W₂.weightGenFun hft₂ := by
-- proof
  classical
  ext n
  rw [PowerSeries.coeff_mul]
  simp only [weightGenFun, PowerSeries.coeff_mk, countOfWeight]
  -- The count of weight n in product equals sum over (i,j) with i+j=n of products of counts
  have hft_prod := prod_isFiniteType W₁ W₂ hft₁ hft₂
  -- Show that the toFinset of the product weight set equals the biUnion of toFinsets
  have key : (hft_prod n).toFinset =
      (antidiagonal n).biUnion (fun ij => (hft₁ ij.1).toFinset ×ˢ (hft₂ ij.2).toFinset) := by
    ext ⟨a, b⟩
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, mem_biUnion, mem_product, prod]
    constructor
    · intro h
      refine ⟨(W₁.weight a, W₂.weight b), ?_, rfl, rfl⟩
      exact (HasAntidiagonal.mem_antidiagonal).mpr h
    · rintro ⟨⟨i, j⟩, hij, ha, hb⟩
      rw [ha, hb]
      exact (HasAntidiagonal.mem_antidiagonal).mp hij
  rw [key]
  -- The biUnion is disjoint, so card equals sum of cards
  have hdisj : (antidiagonal n : Set (ℕ × ℕ)).PairwiseDisjoint
      (fun ij => (hft₁ ij.1).toFinset ×ˢ (hft₂ ij.2).toFinset) := by
    intro ⟨i₁, j₁⟩ _ ⟨i₂, j₂⟩ _ hne
    simp only [Function.onFun, Finset.disjoint_iff_ne]
    intro ⟨a, b⟩ hab ⟨a', b'⟩ hab' heq
    simp only [mem_product, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hab hab'
    apply hne
    simp only [Prod.mk.injEq] at heq
    obtain ⟨ha_eq, hb_eq⟩ := heq
    rw [← hab.1, ← hab.2, ha_eq, hb_eq, hab'.1, hab'.2]
  rw [card_biUnion hdisj]
  simp only [card_product]
  -- Convert ↑(∑ ...) to ∑ ↑(...)
  push_cast
  rfl


-- created on 2026-10-20
