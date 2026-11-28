module

public import Mathlib.Data.Matrix.Basic

@[expose] public section

/--
Vertical concatenation of two matrices along the row axis.

For `A : Matrix (Fin m) (Fin n) α` and `B : Matrix (Fin m') (Fin n) α`, the result
`vstack A B` is the `(m + m') × n` matrix whose rows are those of `A` followed by
those of `B`, columns aligned:

\[
  \mathrm{vstack}\ A\ B =
  \begin{bmatrix}
    A \\
    B
  \end{bmatrix}
\]

so `(vstack A B) i j` is `A ⟨i, ·⟩ j` when `i < m`, and `B ⟨i - m, ·⟩ j`
otherwise.
-/
def Matrix.vstack {m m' n : ℕ} {α : Type*}
    (A : Matrix (Fin m) (Fin n) α) (B : Matrix (Fin m') (Fin n) α) :
    Matrix (Fin (m + m')) (Fin n) α :=
  Matrix.of fun i j =>
    if h : (i : ℕ) < m then
      A ⟨i, h⟩ j
    else
      B ⟨(i : ℕ) - m, by
        have hi : (i : ℕ) < m + m' := i.isLt
        omega⟩ j
