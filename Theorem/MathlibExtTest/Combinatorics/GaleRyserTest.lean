/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/GaleRyserTest.lean -/


import Def.Combinatorics.GaleRyser
import Lemma.Finset.GaleRyser


namespace MetaMathlibExt

open MathlibExt.Combinatorics.GaleRyserWanted

/-- The public characteristic lemma expresses `prefixSum` as a sum over
`Fin k`, without unfolding the `Finset.range`/`dite` implementation. -/
example {m : ℕ} (r : Fin m → ℕ) {k : ℕ} (hk : k ≤ m) :
    prefixSum r k = ∑ i : Fin k, r ⟨i.val, lt_of_lt_of_le i.2 hk⟩ :=
  prefixSum_eq_sum_fin r hk

/-- Rewriting with the characteristic lemma inside the `gale_ryser`
right-hand-side shape. -/
example {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) {k : ℕ} (hk : k ≤ m)
    (h : prefixSum r k ≤ ∑ j : Fin n, min k (c j)) :
    ∑ i : Fin k, r ⟨i.val, lt_of_lt_of_le i.2 hk⟩ ≤ ∑ j : Fin n, min k (c j) := by
  rwa [prefixSum_eq_sum_fin r hk] at h

/-- A concrete evaluation via the characteristic lemma. -/
example : prefixSum (fun i : Fin 3 => 7 + i.val) 2 = 15 := by
  rw [prefixSum_eq_sum_fin _ (by decide : 2 ≤ 3)]
  decide

end MetaMathlibExt
