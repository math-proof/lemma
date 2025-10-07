import Lemma.Bool.EqCast.of.HEq
import Lemma.Bool.HEq.of.All_Eq_Cast.Eq.Eq
open Bool


@[main]
private lemma main
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
