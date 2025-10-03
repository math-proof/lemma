import Lemma.List.MapTake.eq.Replicate.of.Le_Length.All_Eq
open List


@[main]
private lemma main
  {i n : ℕ}
  {v : List (List α)}
-- given
  (h₀ : ∀ l ∈ v, l.length = n)
  (h₁ : i ≤ v.length) :
-- imply
  (v.take i).flatten.length = i * n := by
-- proof
  rw [List.length_flatten]
  rw [MapTake.eq.Replicate.of.Le_Length.All_Eq (by assumption) (by assumption), List.sum_replicate]
  rfl


-- created on 2025-06-13
-- updated on 2025-06-14
