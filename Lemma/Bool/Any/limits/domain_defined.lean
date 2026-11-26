import Initialize.Tactic.Attr.Basic
import Lemma.Bool.Any.doit.inner
open Bool


@[path]
private lemma main
  {m n : ℕ}
  {p : ℕ → Prop}
-- given
  (h : m ≤ n) :
-- imply
  (∃ i < m, p i) ↔ ∃ i < min m n, p i := by
-- proof
  rw [min_eq_left h]


-- created on 2026-09-27
-- updated on 2026-11-26
