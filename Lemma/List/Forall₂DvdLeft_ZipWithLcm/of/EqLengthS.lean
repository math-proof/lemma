import sympy.core.mul
import sympy.Basic


@[main]
private lemma main
-- given
  (s s' : List ℕ)
  (h : s.length = s'.length) :
-- imply
  List.Forall₂ (fun a b => a ∣ b) s (s.zipWith Nat.lcm s') := by
-- proof
  induction s generalizing s' with
  | nil =>
    cases s'
    ·
      constructor
    ·
      cases h
  | cons n s ih =>
    cases s' with
    | nil =>
      cases h
    | cons n' s' =>
      exact List.Forall₂.cons (Nat.dvd_lcm_left n n')
        (ih s' (Nat.succ_injective h))


-- created on 2026-10-07
