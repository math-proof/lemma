import Mathlib.Data.Matrix.Mul
import sympy.Basic
open Matrix


@[main]
private lemma main
  {n : Type*}
  [Fintype n]
  {R : Type*}
  [CommSemiring R]
  {W : Matrix n n R}
  {x y : n → R}
-- given
  (h : W.transpose = W) :
-- imply
  x ⬝ᵥ W *ᵥ y = y ⬝ᵥ W *ᵥ x := by
-- proof
  simpa [h] using dotProduct_transpose_mulVec W x y


-- created on 2021-01-04
-- updated on 2023-05-21
