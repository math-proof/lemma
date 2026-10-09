import sympy.sets.sets
import sympy.Basic


@[path]
private lemma given
  {n : ℕ}
  {a b : ℕ → ℤ}
-- given
  (h : ∀ k, a k = b k) :
-- imply
  (Finset.range n).biUnion (fun k => {a k}) = (Finset.range n).biUnion (fun k => {b k}) := by
-- proof
  simp only [h]


-- created on 2021-03-29
