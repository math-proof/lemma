import Mathlib
import sympy.Basic
import sympy.concrete.InclusionExclusion1
open Finset Nat
open scoped BigOperators
open AlgebraicCombinatorics.InclusionExclusion


/--
[InclusionExclusion1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/InclusionExclusion1.lean)
-/
@[path]
private lemma pie_size_version
  [DecidableEq α] [Fintype α]
-- given
  (s : Finset ι)
  (A : ι → Finset α) :
-- imply
  (s.inf fun i => (A i)ᶜ).card = ∑ I ∈ s.powerset, (-1 : ℤ) ^ #I * #(I.inf A) := by
-- proof
  apply AlgebraicCombinatorics.InclusionExclusion.pie_size_version

/--
[InclusionExclusion1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/InclusionExclusion1.lean)
-/
@[path]
private lemma pie_size_version'
  [DecidableEq α] [Fintype α]
-- given
  (s : Finset ι)
  (A : ι → Finset α) :
-- imply
  ((s.biUnion A)ᶜ).card = ∑ I ∈ s.powerset, (-1 : ℤ) ^ #I * #(I.inf A) := by
-- proof
  apply AlgebraicCombinatorics.InclusionExclusion.pie_size_version'

/--
[InclusionExclusion1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/InclusionExclusion1.lean)
-/
@[path]
private lemma pie_size_version_fin
  [DecidableEq α] [Fintype α]
-- given
  (n : ℕ)
  (A : Fin n → Finset α) :
-- imply
  (Finset.univ.inf fun i => (A i)ᶜ).card =
    ∑ I ∈ Finset.univ.powerset, (-1 : ℤ) ^ #I * #(I.inf A) := by
-- proof
  apply AlgebraicCombinatorics.InclusionExclusion.pie_size_version_fin

/--
[InclusionExclusion1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/InclusionExclusion1.lean)
-/
@[path]
private lemma pie_rule_breaking
  [DecidableEq α] [Fintype α]
-- given
  (n : ℕ)
  (satisfiesRule : Fin n → Finset α) :
-- imply
  (Finset.univ.filter fun u => ∀ i : Fin n, u ∉ satisfiesRule i).card =
    ∑ I ∈ Finset.univ.powerset, (-1 : ℤ) ^ #I *
      (Finset.univ.filter fun u => ∀ i ∈ I, u ∈ satisfiesRule i).card := by
-- proof
  apply AlgebraicCombinatorics.InclusionExclusion.pie_rule_breaking

/--
[InclusionExclusion1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/InclusionExclusion1.lean)
-/
@[path]
private lemma card_functions_avoiding_set
-- given
  (m n : ℕ)
  (I : Finset (Fin n)) :
-- imply
  Fintype.card (Subtype fun f : Fin m → Fin n => ∀ i ∈ I, i ∉ Set.range f) = (n - #I) ^ m := by
-- proof
  apply AlgebraicCombinatorics.InclusionExclusion.card_functions_avoiding_set

/--
[InclusionExclusion1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/InclusionExclusion1.lean)
-/
@[path]
private lemma numSurj_formula
-- given
  (m n : ℕ) :
-- imply
  (numSurj m n : ℤ) = ∑ k ∈ range (n + 1), (-1 : ℤ) ^ k * (n.choose k) * (n - k) ^ m := by
-- proof
  apply AlgebraicCombinatorics.InclusionExclusion.numSurj_formula

/--
[InclusionExclusion1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/InclusionExclusion1.lean)
-/
@[path]
private lemma surjOn_alternating_sum_eq_zero
-- given
  (n m : ℕ)
  (h : m < n) :
-- imply
  ∑ k ∈ range (n + 1), (-1 : ℤ) ^ k * (n.choose k) * (n - k) ^ m = 0 := by
-- proof
  apply AlgebraicCombinatorics.InclusionExclusion.surjOn_alternating_sum_eq_zero n m h

/--
[InclusionExclusion1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/InclusionExclusion1.lean)
-/
@[path]
private lemma surjOn_alternating_sum_eq_factorial
-- given
  (n : ℕ) :
-- imply
  ∑ k ∈ range (n + 1), (-1 : ℤ) ^ k * (n.choose k) * (n - k) ^ n = n ! := by
-- proof
  apply AlgebraicCombinatorics.InclusionExclusion.surjOn_alternating_sum_eq_factorial

/--
[InclusionExclusion1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/InclusionExclusion1.lean)
-/
@[path]
private lemma surjOn_alternating_sum_nonneg
-- given
  (m n : ℕ) :
-- imply
  0 ≤ ∑ k ∈ range (n + 1), (-1 : ℤ) ^ k * (n.choose k) * (n - k) ^ m := by
-- proof
  apply AlgebraicCombinatorics.InclusionExclusion.surjOn_alternating_sum_nonneg

/--
[InclusionExclusion1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/InclusionExclusion1.lean)
-/
@[path]
private lemma surjective_smul
-- given
  {f : Fin m → Fin n}
  (hf : Function.Surjective f)
  (σ : Equiv.Perm (Fin n)) :
-- imply
  Function.Surjective (σ • f) := by
-- proof
  apply AlgebraicCombinatorics.InclusionExclusion.surjective_smul σ hf

/--
[InclusionExclusion1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/InclusionExclusion1.lean)
-/
@[path]
private lemma stabilizer_surj_eq_bot
-- given
  (f : Subtype fun f : Fin m → Fin n => Function.Surjective f) :
-- imply
  MulAction.stabilizer (Equiv.Perm (Fin n)) f = ⊥ := by
-- proof
  apply AlgebraicCombinatorics.InclusionExclusion.stabilizer_surj_eq_bot

/--
[InclusionExclusion1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/InclusionExclusion1.lean)
-/
@[path]
private lemma factorial_dvd_numSurj
-- given
  (m n : ℕ) :
-- imply
  n ! ∣ numSurj m n := by
-- proof
  apply AlgebraicCombinatorics.InclusionExclusion.factorial_dvd_numSurj

/--
[InclusionExclusion1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/InclusionExclusion1.lean)
-/
@[path]
private lemma surjOn_alternating_sum_dvd_factorial
-- given
  (m n : ℕ) :
-- imply
  (n ! : ℤ) ∣ ∑ k ∈ range (n + 1), (-1 : ℤ) ^ k * (n.choose k) * (n - k) ^ m := by
-- proof
  apply AlgebraicCombinatorics.InclusionExclusion.surjOn_alternating_sum_dvd_factorial

/--
[InclusionExclusion1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/InclusionExclusion1.lean)
-/
@[path]
private lemma mem_derangements
-- given
  {α : Type*}
  (σ : Derangement α) :
-- imply
  σ.val ∈ derangements α := by
-- proof
  apply AlgebraicCombinatorics.InclusionExclusion.Derangement.mem_derangements

/--
[InclusionExclusion1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/InclusionExclusion1.lean)
-/
@[path]
private lemma id_of_isEmpty
  [IsEmpty α] :
-- imply
  ∃ d : Derangement α, d.val = 1 := by
-- proof
  apply AlgebraicCombinatorics.InclusionExclusion.Derangement.id_of_isEmpty

/--
[InclusionExclusion1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/InclusionExclusion1.lean)
-/
@[path]
private lemma id_not_derangement
  [Nonempty α] :
-- imply
  ∀ d : Derangement α, d.val ≠ 1 := by
-- proof
  apply AlgebraicCombinatorics.InclusionExclusion.Derangement.id_not_derangement

/--
[InclusionExclusion1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/InclusionExclusion1.lean)
-/
@[path]
private lemma card_Derangement_eq
-- given
  (n : ℕ) :
-- imply
  Fintype.card (Derangement (Fin n)) = numDerangements n := by
-- proof
  apply AlgebraicCombinatorics.InclusionExclusion.card_Derangement_eq

/--
[InclusionExclusion1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/InclusionExclusion1.lean)
-/
@[path]
private lemma numDerangements_two' :
-- imply
  numDerangements 2 = 1 := by
-- proof
  apply AlgebraicCombinatorics.InclusionExclusion.numDerangements_two'

/--
[InclusionExclusion1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/InclusionExclusion1.lean)
-/
@[path]
private lemma numDerangements_three :
-- imply
  numDerangements 3 = 2 := by
-- proof
  apply AlgebraicCombinatorics.InclusionExclusion.numDerangements_three

/--
[InclusionExclusion1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/InclusionExclusion1.lean)
-/
@[path]
private lemma numDerangements_four :
-- imply
  numDerangements 4 = 9 := by
-- proof
  apply AlgebraicCombinatorics.InclusionExclusion.numDerangements_four

/--
[InclusionExclusion1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/InclusionExclusion1.lean)
-/
@[path]
private lemma numDerangements_five :
-- imply
  numDerangements 5 = 44 := by
-- proof
  apply AlgebraicCombinatorics.InclusionExclusion.numDerangements_five

/--
[InclusionExclusion1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/InclusionExclusion1.lean)
-/
@[path]
private lemma numDerangements_formula
-- given
  (n : ℕ) :
-- imply
  (numDerangements n : ℤ) =
    ∑ k ∈ range (n + 1), (-1 : ℤ) ^ k * (n.choose k) * (n - k)! := by
-- proof
  apply AlgebraicCombinatorics.InclusionExclusion.numDerangements_formula

/--
[InclusionExclusion1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/InclusionExclusion1.lean)
-/
@[path]
private lemma numDerangements_formula_rat
-- given
  (n : ℕ) :
-- imply
  (numDerangements n : ℚ) = n ! * ∑ k ∈ range (n + 1), (-1 : ℚ) ^ k / k ! := by
-- proof
  apply AlgebraicCombinatorics.InclusionExclusion.numDerangements_formula_rat

/--
[InclusionExclusion1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/InclusionExclusion1.lean)
-/
@[path]
private lemma totient_eq_prod_one_sub_inv
-- given
  (c : ℕ)
  (hc : 0 < c) :
-- imply
  (Nat.totient c : ℚ) = c * ∏ p ∈ c.primeFactors, (1 - 1 / (p : ℚ)) := by
-- proof
  apply AlgebraicCombinatorics.InclusionExclusion.totient_eq_prod_one_sub_inv c hc

/--
[InclusionExclusion1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/InclusionExclusion1.lean)
-/
@[path]
private lemma weighted_pie
  [Fintype ι] [DecidableEq ι] [Fintype U] [DecidableEq U] [AddCommGroup G]
-- given
  (A : ι → Finset U)
  (w : U → G) :
-- imply
  ∑ u ∈ Finset.univ.inf fun i => (A i)ᶜ, w u =
    ∑ I ∈ Finset.univ.powerset, (-1 : ℤ) ^ I.card • ∑ u ∈ I.inf A, w u := by
-- proof
  apply AlgebraicCombinatorics.InclusionExclusion.weighted_pie

/--
[InclusionExclusion1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/InclusionExclusion1.lean)
-/
@[path]
private lemma weighted_pie'
  [DecidableEq ι] [Fintype U] [DecidableEq U] [AddCommGroup G]
-- given
  (s : Finset ι)
  (A : ι → Finset U)
  (w : U → G) :
-- imply
  ∑ u ∈ s.inf fun i => (A i)ᶜ, w u =
    ∑ I ∈ s.powerset, (-1 : ℤ) ^ I.card • ∑ u ∈ I.inf A, w u := by
-- proof
  apply AlgebraicCombinatorics.InclusionExclusion.weighted_pie'

/--
[InclusionExclusion1](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/InclusionExclusion1.lean)
-/
@[path]
private lemma size_pie_from_weighted
  [DecidableEq ι] [Fintype U] [DecidableEq U]
-- given
  (s : Finset ι)
  (A : ι → Finset U) :
-- imply
  ((s.inf fun i => (A i)ᶜ).card : ℤ) =
    ∑ I ∈ s.powerset, (-1 : ℤ) ^ I.card * (I.inf A).card := by
-- proof
  apply AlgebraicCombinatorics.InclusionExclusion.size_pie_from_weighted


-- created on 2026-10-20
