import Notation.Analysis.Complex.Complexes
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ}
  {z : ℕ → ℂ} :
-- imply
  ∑ k ∈ Finset.range n, im (z k) = im (∑ k ∈ Finset.range n, z k) := by
-- proof
  exact (Complex.im_sum _ _).symm


-- created on 2023-06-03
