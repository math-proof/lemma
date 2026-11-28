module

public import Mathlib.Data.Matrix.Basic

@[expose] public section

/--
Horizontal concatenation of two matrices along the column axis.

For `A : Matrix (Fin m) (Fin n) α` and `B : Matrix (Fin m) (Fin n') α`, the result
`hstack A B` is the `m × (n + n')` matrix whose columns are those of `A` followed
by those of `B`, rows aligned:

\[
  \mathrm{hstack}\ A\ B =
  \begin{bmatrix}
    A & B
  \end{bmatrix}
\]

so `(hstack A B) i j` is `A i ⟨j, ·⟩` when `j < n`, and `B i ⟨j - n, ·⟩`
otherwise.
-/
def Matrix.hstack {m n n' : ℕ} {α : Type*}
    (A : Matrix (Fin m) (Fin n) α) (B : Matrix (Fin m) (Fin n') α) :
    Matrix (Fin m) (Fin (n + n')) α :=
  Matrix.of fun i j =>
    if h : (j : ℕ) < n then
      A i ⟨j, h⟩
    else
      B i ⟨(j : ℕ) - n, by
        have hj : (j : ℕ) < n + n' := j.isLt
        omega⟩
