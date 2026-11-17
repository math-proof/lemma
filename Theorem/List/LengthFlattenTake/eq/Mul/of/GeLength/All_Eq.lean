module

public import Theorem.List.MapTake.eq.Replicate.of.GeLength.All_Eq

public section

open List


public theorem List.LengthFlattenTake.eq.Mul.of.GeLength.All_Eq
  {i n : ℕ}
  {s : List (List α)}
-- given
  (h₀ : ∀ l ∈ s, l.length = n)
  (h₁ : s.length ≥ i) :
-- imply
  (s.take i).flatten.length = i * n := by
-- proof
  rw [List.length_flatten]
  rw [MapTake.eq.Replicate.of.GeLength.All_Eq (by assumption) (by assumption), List.sum_replicate]
  rfl


-- created on 2025-06-13
-- updated on 2025-06-14
