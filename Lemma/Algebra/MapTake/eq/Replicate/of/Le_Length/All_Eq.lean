import Lemma.Algebra.Eq_Replicate.is.EqLength.All_Eq
open Algebra


@[main]
private lemma main
  {n : ℕ}
  {v : List (List α)}
-- given
  (h₀ : ∀ l ∈ v, l.length = n)
  (h₁ : i ≤ v.length) :
-- imply
  (v.take i).map List.length = List.replicate i n := by
-- proof
  refine Eq_Replicate.of.EqLength.All_Eq ?_ ?_
  ·
    simp [h₁]
  ·
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨l, ⟨hl_mem, rfl⟩⟩ := hx
    apply h₀ l
    apply List.mem_of_mem_take hl_mem


-- created on 2025-06-14
-- updated on 2025-08-02
