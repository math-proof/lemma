import Lemma.Bool.HEq.of.All_HEq.Eq
open Bool


@[main]
private lemma main
  {f : α → β}
  {g : α' → β}
-- given
  (h_all : ∀ (a : α), HEq (f a) (g (cast h a))) :
-- imply
  HEq f g := by
-- proof
  apply HEq.of.All_HEq.Eq <;>
    simp_all


-- created on 2025-07-16
