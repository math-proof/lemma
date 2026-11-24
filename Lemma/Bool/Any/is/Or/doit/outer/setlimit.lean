import Initialize.Tactic.Attr.Basic
import Lemma.Bool.Any.is.Or.doit.outer


@[path]
private lemma main
  [DecidableEq ι]
  {x : ι → ℕ → ℝ}
  {f : ι → ℕ}
  {a b : ι}
-- given
  (h : a ≠ b) :
-- imply
  ∑ i ∈ ({a, b} : Finset ι), ∑ j ∈ Finset.range (f i), x i j = ∑ j ∈ Finset.range (f a), x a j + ∑ j ∈ Finset.range (f b), x b j := by
-- proof
  rw [Finset.sum_pair h]


-- created on 2019-02-22
-- updated on 2026-11-24
