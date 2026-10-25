/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Additive/Szemeredi.lean -/


import Def.Combinatorics.Additive.Szemeredi
import Lemma.Finset.Additive.Szemeredi
import Mathlib.Tactic


namespace MathlibExtTest.Combinatorics.Additive.Szemeredi

-- Every Boolean coloring has arbitrarily long monochromatic arithmetic progressions.
example (k : ℕ) (hk : 0 < k) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ c : ℕ → Bool,
      ∃ b : Bool, ∃ a d : ℕ, 0 < d ∧ ∀ i : ℕ, i < k → c (a + i * d) = b := by
  obtain ⟨N, hN⟩ :=
    MathlibExt.Combinatorics.Additive.SzemerediWanted.szemeredi
      k hk (1 / 2) (by norm_num)
  refine ⟨N, ?_⟩
  intro n hn c
  let T := (Finset.range n).filter fun j => c j = true
  let F := (Finset.range n).filter fun j => c j = false
  have hTsub : T ⊆ Finset.range n := Finset.filter_subset _ _
  have hFsub : F ⊆ Finset.range n := Finset.filter_subset _ _
  have hpart : T.card + F.card = n := by
    simpa [T, F] using
      Finset.card_filter_add_card_filter_not (s := Finset.range n) (fun j => c j = true)
  by_cases hT : (1 / 2 : ℝ) * (n : ℝ) ≤ (T.card : ℝ)
  · obtain ⟨a, d, hd, ha⟩ := hN n hn T hTsub hT
    refine ⟨true, a, d, hd, ?_⟩
    intro i hi
    exact (Finset.mem_filter.mp (ha i hi)).2
  · have hpartReal : (T.card : ℝ) + (F.card : ℝ) = (n : ℝ) := by
      exact_mod_cast hpart
    have hF : (1 / 2 : ℝ) * (n : ℝ) ≤ (F.card : ℝ) := by
      nlinarith
    obtain ⟨a, d, hd, ha⟩ := hN n hn F hFsub hF
    refine ⟨false, a, d, hd, ?_⟩
    intro i hi
    exact (Finset.mem_filter.mp (ha i hi)).2

end MathlibExtTest.Combinatorics.Additive.Szemeredi
