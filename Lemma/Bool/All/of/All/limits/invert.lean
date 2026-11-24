import Initialize.Tactic.Attr.Basic
import Lemma.Bool.All.of.All.limits.insert


@[path]
private lemma main
  {f g : α → Prop}
-- given
  (h : ∀ e, g e → f e) :
-- imply
  ∀ e, ¬f e → ¬g e :=
-- proof
  fun e hf hg => hf (h e hg)




-- created on 2024-06-25
-- updated on 2026-11-24
