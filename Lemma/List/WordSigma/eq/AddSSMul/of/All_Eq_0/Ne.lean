import Mathlib
import Mathlib.Data.List.Chain
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.CoxeterGroup.ParabolicPositivity
open Finset BigOperators CoxeterGroup


/--
[wordSigma_linear_combination](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/ParabolicPositivity.lean)
-/
@[path]
private lemma wordSigma_linear_combination_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
  {word : List B}
  {v : B → ℝ}
-- given
  (hst : s ≠ t)
  (hsupp : ∀ u, u ≠ s → u ≠ t → v u = 0) :
-- imply
  wordSigma M word v = v s • wordSigma M word (e s) + v t • wordSigma M word (e t) := by
-- proof
  apply CoxeterGroup.wordSigma_linear_combination M s t hst word v hsupp

/--
[alternating_word_canonical](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/ParabolicPositivity.lean)
-/
@[path]
private lemma alternating_word_canonical_eq
  [DecidableEq B]
  [Fintype B]
  {s t : B}
  {word : List B}
-- given
  (hst : s ≠ t)
  (halt : ∀ b ∈ word, b = s ∨ b = t)
  (hchain : List.IsChain (· ≠ ·) word)
  (hlast : word = [] ∨ (∃ h : word ≠ [], word.getLast h = t)) :
-- imply
  (∃ k, word = altWordEven s t k) ∨ (∃ k, word = t :: altWordEven s t k) := by
-- proof
  apply CoxeterGroup.alternating_word_canonical s t hst word halt hchain hlast

/--
[parabolic_pos_of_canon](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/ParabolicPositivity.lean)
-/
@[path]
private lemma parabolic_pos_of_canon_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
  {word : List B}
-- given
  (hst : s ≠ t)
  (hlen : word.length < M s t ∨ M s t = 0)
  (hcanon : (∃ k, word = altWordEven s t k) ∨ (∃ k, word = t :: altWordEven s t k)) :
-- imply
  IsPositive (wordSigma M word (e s)) := by
-- proof
  apply CoxeterGroup.parabolic_pos_of_canon M s t hst word hlen hcanon

/--
[parabolic_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/ParabolicPositivity.lean)
-/
@[path]
private lemma parabolic_pos_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
  {word : List B}
-- given
  (hst : s ≠ t)
  (halt : ∀ b ∈ word, b = s ∨ b = t)
  (hlen : word.length < M s t ∨ M s t = 0)
  (hchain : List.IsChain (· ≠ ·) word)
  (hlast : word = [] ∨ (∃ h : word ≠ [], word.getLast h = t)) :
-- imply
  IsPositive (wordSigma M word (e s)) := by
-- proof
  apply CoxeterGroup.parabolic_pos M s t hst word halt hlen hchain hlast

/--
[parabolic_pos_vector_of_both_positive](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/ParabolicPositivity.lean)
-/
@[path]
private lemma parabolic_pos_vector_of_both_positive_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s t : B}
  {word : List B}
  {v : B → ℝ}
-- given
  (hst : s ≠ t)
  (hpos_s : IsPositive (wordSigma M word (e s)))
  (hpos_t : IsPositive (wordSigma M word (e t)))
  (hpos : IsPositive v)
  (hsupp : ∀ u, u ≠ s → u ≠ t → v u = 0) :
-- imply
  IsPositive (wordSigma M word v) := by
-- proof
  apply CoxeterGroup.parabolic_pos_vector_of_both_positive M s t hst word hpos_s hpos_t v hpos hsupp


-- created on 2026-10-23
