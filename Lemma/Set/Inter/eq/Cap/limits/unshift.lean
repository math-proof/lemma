import sympy.Basic
import Mathlib


@[path]
private lemma main
  {f : ℕ → Set α}
  {i n : ℕ}
-- given
  (h : i < n) :
-- imply
  (⋂ k ∈ Finset.Ico (i + 1) n, f k) ∩ f i = ⋂ k ∈ Finset.Ico i n, f k := by
-- proof
  have h' : Finset.Ico i n = insert i (Finset.Ico (i + 1) n) := by
    ext k
    simp only [Finset.mem_Ico, Finset.mem_insert]
    omega
  rw [h', Finset.set_biInter_insert, Set.inter_comm]


-- created on 2021-04-27
