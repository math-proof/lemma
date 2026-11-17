module

public import Theorem.Nat.Le.of.Lt

public section

open Nat


public theorem Nat.Le.of.Prod.eq.IteGt
  [LinearOrder α]
  {a b a' b' : α}
-- given
  (h : (⟨a', b'⟩ : α × α) = if a > b then
    ⟨b, a⟩
  else
    ⟨a, b⟩) :
-- imply
  a' ≤ b' := by
-- proof
  by_cases h : a > b <;> 
    simp_all
  apply Le.of.Lt h


-- created on 2025-06-19
