import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet


/--
[weight_gen_fun_eq_of_isomorphic_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
  [CommSemiring R]
-- given
  {α β : Type*}
  (W₁ : WeightedSet α)
  (W₂ : WeightedSet β)
  (hft₁ : W₁.IsFiniteType)
  (hft₂ : W₂.IsFiniteType)
  (h : AreIsomorphic W₁ W₂) :
-- imply
  W₁.weightGenFun (R := R) hft₁ = W₂.weightGenFun hft₂ := by
-- proof
  obtain ⟨iso⟩ := h
  ext n
  simp only [weightGenFun, coeff_mk, countOfWeight]
  congr 1
  rw [← Nat.card_eq_card_finite_toFinset (hft₁ n), ← Nat.card_eq_card_finite_toFinset (hft₂ n)]
  apply Nat.card_congr
  refine Equiv.subtypeEquiv iso.toEquiv ?_
  intro a
  simp only [Set.mem_ofPred_eq]
  rw [iso.weight_eq]


-- created on 2026-10-20
