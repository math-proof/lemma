import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic
import Lemma.Bool.Any.of.Any.limits.relax
open Bool


@[path]
private lemma main
  {m n : ℕ}
  {p : ℕ → Prop}
-- given
  (h : ∃ i < min m n, p i) :
-- imply
  ∃ i < m, p i := by
-- proof
  obtain ⟨i, hi, hp⟩ := h
  simp only [lt_min_iff] at hi
  exact ⟨i, hi.1, hp⟩


-- created on 2026-09-27
-- updated on 2026-11-26
