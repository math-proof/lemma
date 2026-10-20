import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Sequences.GeneralizedEuclidSequence
open scoped Pointwise
open MetaMathlibExt


/--
[generalized_euclid_sequence_contains_every_prime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Sequences/GeneralizedEuclidSequence.lean)
-/
@[path]
private lemma generalized_euclid_sequence_contains_every_prime_eq
  {P : Finset ℕ}
-- given
  (hP : ∀ p ∈ P, Nat.Prime p) :
-- imply
  ∃ a : ℕ → ℕ, (∀ i, Nat.Prime (a i)) ∧ Function.Injective a ∧
    (∀ i < P.card, a i ∈ P) ∧ (∀ p ∈ P, ∃ i < P.card, a i = p) ∧
    (∀ n, P.card ≤ n → ∃ I : Finset ℕ, I ⊆ Finset.range n ∧
    a n ∣ (∏ i ∈ I, a i) + ∏ i ∈ (Finset.range n \ I), a i) ∧
    (∀ p, Nat.Prime p → ∃ i, a i = p) := by
-- proof
  apply MetaMathlibExt.generalized_euclid_sequence_contains_every_prime P hP


-- created on 2026-10-20
