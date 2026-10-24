/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Sequences/GeneralizedEuclidSequence.lean -/


import sympy.atlas.NumberTheory.Sequences.GeneralizedEuclidSequence
import Lemma.Nat.Sequences.GeneralizedEuclidSequence

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime


namespace MathlibExtTest.NumberTheory.Sequences.GeneralizedEuclidSequence

-- Starting from `2, 3`, the sequence reaches `7` after the seed and supplies its Euclid witness.
example : ∃ (a : ℕ → ℕ) (i : ℕ), 2 ≤ i ∧ a i = 7 ∧
    ∃ I : Finset ℕ, I ⊆ Finset.range i ∧
      a i ∣ (∏ j ∈ I, a j) + ∏ j ∈ (Finset.range i \ I), a j := by
  have hseed : ∀ p ∈ ({2, 3} : Finset ℕ), p.Prime := by
    norm_num
  obtain ⟨a, _hprime, _hinj, hfirst, _hseedCover, hstep, hcover⟩ :=
    MetaMathlibExt.generalized_euclid_sequence_contains_every_prime {2, 3} hseed
  obtain ⟨i, hi⟩ := hcover 7 (by norm_num)
  have hi2 : 2 ≤ i := by
    by_contra hlt
    have hiSeed : i < ({2, 3} : Finset ℕ).card := by
      simpa using Nat.lt_of_not_ge hlt
    have hmem := hfirst i hiSeed
    rw [hi] at hmem
    norm_num at hmem
  obtain ⟨I, hI, hdvd⟩ := hstep i (by simpa using hi2)
  exact ⟨a, i, hi2, hi, I, hI, hdvd⟩

end MathlibExtTest.NumberTheory.Sequences.GeneralizedEuclidSequence
