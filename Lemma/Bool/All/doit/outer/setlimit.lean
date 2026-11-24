import Initialize.Tactic.Attr.Basic
import Lemma.Bool.All.limits.swap.subst


@[path]
private lemma main
  {a : ι}
  {q p : ι → κ → Prop} :
-- imply
  (∀ i ∈ ({a} : Set ι), ∀ j, q i j → p i j) ↔ ∀ j, q a j → p a j := by
-- proof
  simp


-- created on 2018-12-05
-- updated on 2026-11-24
