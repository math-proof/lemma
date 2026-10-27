import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Misc.erdos_613.Part7
open Classical
open scoped BigOperators
open PikhurkoN5.V
open PikhurkoN5
open PikhurkoN5.Finset


/--
[exists_subset_card_eq](https://github.com/teorth/analysis/blob/main/Analysis/Misc/erdos_613.lean)
-/
@[path]
private lemma main
  {s : Finset α}
  {k : ℕ}
-- given
  (hk : k ≤ s.card) :
-- imply
  ∃ t ⊆ s, t.card = k :=
-- proof
  PikhurkoN5.Finset.exists_subset_card_eq s hk


-- created on 2026-10-22
