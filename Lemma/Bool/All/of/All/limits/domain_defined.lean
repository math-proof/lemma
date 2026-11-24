import Initialize.Tactic.Attr.Basic
import Lemma.Bool.All.of.All.limits.domain_defined.given


@[path]
private lemma main
  {m n : ℕ}
  {p : ℕ → Prop}
-- given
  (h : ∀ i ∈ Finset.range m, p i) :
-- imply
  ∀ i ∈ Finset.range (min m n), p i := by
-- proof
  intro i hi
  simp only [Finset.mem_range, lt_min_iff] at hi
  exact h i (Finset.mem_range.mpr hi.1)




-- created on 2024-06-25
-- updated on 2026-11-24
