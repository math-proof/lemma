import Initialize.Tactic.Attr.Basic
import Lemma.Bool.Any.is.Or.doit.outer
open Bool


@[path]
private lemma main
  [DecidableEq ι]
  {x : ι → ℕ → ℝ}
  {f : ι → ℕ}
  {a b : ι}
-- given
  (h : a ≠ b) :
-- imply
  ∑ i ∈ ({a, b} : Finset ι), ∑ j < (f i), x i j = ∑ j < (f a), x a j + ∑ j < (f b), x b j := by
-- proof
  rw [Finset.sum_pair h]


-- created on 2019-02-22
-- updated on 2026-11-26
