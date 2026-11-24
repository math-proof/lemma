import Initialize.Tactic.Attr.Basic
import Lemma.Bool.All.of.All.limits.swap


@[path]
private lemma main
  {A : Set α}
  {B : Set β}
  {f : α → β → Prop}
-- given
  (h : ∀ y, ∀ x ∈ A, f x y) :
-- imply
  ∀ y ∈ B, ∀ x ∈ A, f x y :=
-- proof
  fun y _ => h y




-- created on 2024-06-25
-- updated on 2026-11-24
