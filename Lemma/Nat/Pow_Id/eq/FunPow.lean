import sympy.core.power
import sympy.Basic


@[main]
private lemma main
  [HPow α Nat α]
-- given
  (γ : α) :
-- imply
  γ ^ (id : Nat → Nat) = fun k ↦ γ ^ k := by
-- proof
  exact rfl


-- created on 2026-10-07
