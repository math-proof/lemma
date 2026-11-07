import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Matrix.Basic
import Class.Analysis.SpecialFunctions.Exponential


/-!
# Softmax of a matrix

Axis softmax for `Matrix m n α`, in the sense of
[`torch.nn.functional.softmax`](https://pytorch.org/docs/stable/generated/torch.nn.functional.softmax.html)
on a rank-2 tensor.

Mathlib has no `Matrix.softmax`. Scalar `sigmoid` is
`Mathlib/Analysis/SpecialFunctions/Sigmoid.lean`; analysis on matrices is
`Mathlib/Analysis/Matrix/`. This definition is the corresponding file
`Def/Analysis/Matrix/Softmax.lean`.

* `axis = 0` normalizes each column (sum over the row index).
* `axis = 1` normalizes each row (sum over the column index).
-/

/-- Softmax along `axis`, where `axis = 0` or `axis = 1`. -/
def Matrix.softmax {m n α : Type*} [Fintype m] [Fintype n] [Exp α]
    (A : Matrix m n α) (axis : ℕ) (h : axis = 0 ∨ axis = 1 := by omega) : Matrix m n α :=
  if h0 : axis = 0 then
    Matrix.of fun i j => Exp.exp (A i j) / ∑ i' : m, Exp.exp (A i' j)
  else
    have : axis = 1 := Or.resolve_left h h0
    Matrix.of fun i j => Exp.exp (A i j) / ∑ j' : n, Exp.exp (A i j')
