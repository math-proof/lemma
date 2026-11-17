module

public import Theorem.Bool.EqCast.of.HEq
public import Theorem.Bool.HEq.of.All_Eq_Cast.Eq.Eq

public section

open Bool


public theorem Bool.HEq.of.All_HEq.Eq
  {f : α → β}
  {g : α' → β'}
-- given
  (h₀ : β = β')
  (h₁ : ∀ (a : α), HEq (f a) (g (cast h a))) :
-- imply
  HEq f g := by
-- proof
  apply HEq.of.All_Eq_Cast.Eq.Eq
  ·
    intro a
    apply Eq_Cast.of.HEq
    specialize h₁ a
    assumption
  ·
    assumption


-- created on 2025-07-16
