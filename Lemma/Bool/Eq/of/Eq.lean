import Initialize.Tactic.Attr.Basic
import Lemma.Bool.Eq.of.Eq.reverse.given


@[path]
private lemma main
  [Coe α β]
  {x y : α}
-- given
  (h : x = y) :
-- imply
  (x : β) = (y : β) := by
-- proof
  rw [h]


@[path]
private lemma swap
  {F G : α → α → β}
-- given
  (h : ∀ x y, F x y = G x y) :
-- imply
  ∀ x y, F y x = G y x :=
-- proof
  fun x y => h y x


-- created on 2019-03-29
-- updated on 2026-10-26
