module

public import Theorem.Nat.Le.of.Prod.eq.IteGt
public import Theorem.Nat.Lt.is.Le.Ne
public import Theorem.Bool.UFn.of.Eq

public section

open Bool Nat


public theorem Nat.Lt.of.Prod.eq.IteGt.Ne
  [LinearOrder α]
  {a b a' b' : α}
-- given
  (h₀ : a ≠ b)
  (h₁ : (⟨a', b'⟩ : α × α) = if a > b then
    ⟨b, a⟩
  else
    ⟨a, b⟩) :
-- imply
  a' < b' := by
-- proof
  have := Le.of.Prod.eq.IteGt h₁
  apply Lt.of.Le.Ne this
  by_contra h
  split at h₁ <;>
  ·
    rw [h] at h₁
    have h_1 := UFn.of.Eq h₁ Prod.fst
    simp at h_1
    have h_2 := UFn.of.Eq h₁ Prod.snd
    simp at h_2
    simp_all


-- created on 2025-06-20
