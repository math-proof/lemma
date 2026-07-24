import Lemma.Nat.Max
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
  a' ⊔ b' = a ⊔ b := by
-- proof
  split at h <;>
  ·
    injection h with h_a h_b
    simp_all [Max.comm]


-- created on 2025-06-20
-- updated on 2025-06-21
