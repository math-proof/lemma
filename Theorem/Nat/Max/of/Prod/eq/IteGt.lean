module

public import Theorem.Nat.Max

public section

open Nat


public theorem Nat.Max.of.Prod.eq.IteGt
  [LinearOrder α]
  {a b a' b' : α}
-- given
  (h : (⟨a', b'⟩ : α × α) = if a > b then
    ⟨b, a⟩
  else
    ⟨a, b⟩) :
-- imply
  a' ⊔ b' = a ⊔ b := by
-- proof
  split at h <;>
  ·
    injection h with h_a h_b
    simp_all [Max.comm]


-- created on 2025-06-20
-- updated on 2025-06-21
