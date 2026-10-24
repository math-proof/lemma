import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Sequences.GeneralizedEuclidSequence
open scoped Pointwise
open MetaMathlibExt


namespace MetaMathlibExt

/--
[geneuclid_squarefree_thirty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Sequences/GeneralizedEuclidSequence.lean)
-/
@[path]
private lemma geneuclid_squarefree_thirty : Squarefree 30 := by
  rw [show 30 = (2 * 3) * 5 by norm_num, Nat.squarefree_mul (by decide),
    Nat.squarefree_mul (by decide)]
  exact ⟨⟨Nat.prime_two.squarefree, Nat.prime_three.squarefree⟩,
    Nat.prime_five.squarefree⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[geneuclid_squarefree_two_thousand_three_hundred_ten](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Sequences/GeneralizedEuclidSequence.lean)
-/
@[path]
private lemma geneuclid_squarefree_two_thousand_three_hundred_ten : Squarefree 2310 := by
  rw [show 2310 = (((2 * 3) * 5) * 7) * 11 by norm_num,
    Nat.squarefree_mul (by decide), Nat.squarefree_mul (by decide),
    Nat.squarefree_mul (by decide), Nat.squarefree_mul (by decide)]
  exact ⟨⟨⟨⟨Nat.prime_two.squarefree, Nat.prime_three.squarefree⟩,
    Nat.prime_five.squarefree⟩, Nat.prime_seven.squarefree⟩,
    Nat.prime_eleven.squarefree⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[chainL_good](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Sequences/GeneralizedEuclidSequence.lean)
-/
@[path]
private lemma chainL_good (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (n : ℕ) :
  Good P (chainL P hP n) :=
  (Chain P hP n).2

end MetaMathlibExt

namespace MetaMathlibExt

/--
[prefix_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Sequences/GeneralizedEuclidSequence.lean)
-/
@[path]
private lemma prefix_mem {l₁ l₂ : List ℕ} (h : l₁ <+: l₂) (a : ℕ) (hm : a ∈ l₁) :
  a ∈ l₂ := by
  have heq := List.prefix_iff_eq_append.mp h
  rw [← heq]
  exact List.mem_append.mpr (Or.inl hm)

end MetaMathlibExt

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
-- updated on 2026-10-23
