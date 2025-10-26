import Lemma.Nat.Le.of.Lt
open Nat


@[main]
private lemma main
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
