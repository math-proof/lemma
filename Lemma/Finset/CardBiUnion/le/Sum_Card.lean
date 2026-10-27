import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [DecidableEq β]
  {s : Finset α}
  {t : α → Finset β} :
-- imply
  (s.biUnion t).card ≤ ∑ a ∈ s, (t a).card :=
-- proof
  Finset.card_biUnion_le


-- created on 2020-07-07
-- updated on 2026-10-26
