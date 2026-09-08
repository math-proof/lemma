import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import sympy.Basic


@[main]
private lemma main
  [DecidableEq β]
  {s : Finset α}
  {t : α → Finset β} :
-- imply
  (s.biUnion t).card ≤ ∑ a ∈ s, (t a).card :=
-- proof
  Finset.card_biUnion_le


-- created on 2020-07-07
-- updated on 2026-09-08
