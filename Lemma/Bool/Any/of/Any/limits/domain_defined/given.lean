import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic
import Lemma.Bool.Any.of.Any.limits.relax


@[path]
private lemma main
  {m n : ℕ}
  {p : ℕ → Prop}
-- given
  (h : ∃ i ∈ Finset.range (min m n), p i) :
-- imply
  ∃ i ∈ Finset.range m, p i := by
-- proof
  obtain ⟨i, hi, hp⟩ := h
  simp only [Finset.mem_range, lt_min_iff] at hi
  exact ⟨i, Finset.mem_range.mpr hi.1, hp⟩




-- created on 2026-09-27
-- updated on 2026-11-24
