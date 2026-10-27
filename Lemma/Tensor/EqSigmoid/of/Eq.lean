import Def.Data.Matrix.Lstm
import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x : ℝ}
  {f g : ℝ → ℝ}
-- given
  (h : f x = g x) :
-- imply
  sigmoid (f x) = sigmoid (g x) := by
-- proof
  rw [h]


-- created on 2023-05-25
