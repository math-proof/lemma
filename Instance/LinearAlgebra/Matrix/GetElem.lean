/-
GetElem for Mathlib Matrix so `L[i]` is an `n → α` row and `L[i][j]` reads an entry.
Validity is `True` (indices are typed by `m` / `n`, e.g. `Fin`).

Rows are plain functions. The nested `L[i][j]` on a `Fin d` row goes through the Nat-indexed
`GetElem` of `Instance.Data.Fin.Fun` plus the `Fin → ℕ` coercion, so `getElem_getElem` below is
stated for `Fin`-indexed rows.

Do not add comma GetElem sugar `L[i, j]` here: it collides with List multi-index
`term__[_,_]` from `Syntax.Data.List.List.Part8`. Use nested `L[i][j]` instead.
Distinct from Syntax ofFun sugar `[i < m][j < n] body` (has `<`).
-/

module

public import Mathlib.LinearAlgebra.Matrix.Defs
public import Instance.Data.Fin.Fun

@[expose] public section

namespace Matrix

variable {m n : Type*} {α : Type*}

/-- Row of a matrix as a plain function, so `L[i]` / `L[i][j]` read a row / an entry. -/
instance : GetElem (Matrix m n α) m (n → α) (fun _ _ => True) where
  getElem A i _ := A i

@[simp] theorem getElem_apply (A : Matrix m n α) (i : m) :
    A[i] = A i :=
  rfl

@[simp] theorem getElem_getElem {d : ℕ} {α : Type*} (A : Matrix m (Fin d) α) (i : m)
    (j : Fin d) : A[i][j] = A i j :=
  rfl

end Matrix
