/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/HilbertWaring.lean -/


import Theorem.NumberTheory.HilbertWaring.Part12
import Lemma.Nat.HilbertWaring
import Mathlib.Tactic


namespace MathlibExtTest.NumberTheory.HilbertWaring

open Finset

-- Zero terms can be deleted, leaving at most `g` positive powers.
example (k : ℕ) (hk : 0 < k) :
    ∃ g : ℕ, ∀ n : ℕ, ∃ (x : Fin g → ℕ) (t : Finset (Fin g)),
      #t ≤ g ∧ (∀ i ∈ t, 0 < x i) ∧ n = ∑ i ∈ t, x i ^ k := by
  obtain ⟨g, hg⟩ :=
    MathlibExt.NumberTheory.HilbertWaringWanted.hilbert_waring k hk
  refine ⟨g, fun n ↦ ?_⟩
  obtain ⟨x, hx⟩ := hg n
  let t := (Finset.univ : Finset (Fin g)).filter fun i ↦ x i ≠ 0
  refine ⟨x, t, ?_, ?_, ?_⟩
  · simpa [t] using
      (Finset.card_filter_le (Finset.univ : Finset (Fin g)) fun i ↦ x i ≠ 0)
  · intro i hi
    have hxi : x i ≠ 0 := (Finset.mem_filter.mp hi).2
    omega
  · calc
      n = ∑ i, x i ^ k := hx
      _ = ∑ i ∈ t, x i ^ k := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro i _ hit
        have hxi : x i = 0 := by
          by_contra hxi
          exact hit (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxi⟩)
        simp [hxi, hk.ne']

end MathlibExtTest.NumberTheory.HilbertWaring
