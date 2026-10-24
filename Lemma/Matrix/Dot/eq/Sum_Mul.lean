import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Notation
open EuclideanSpace'


/--
[EuclideanSpace'.dot_apply](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Notation.lean)
-/
@[path]
private lemma main
  {n:ℕ}
  {x y: EuclideanSpace' n} :
-- imply
  x ⬝ y = ∑ i, (x i)*(y i) :=
-- proof
  EuclideanSpace'.dot_apply x y


-- created on 2026-10-22
