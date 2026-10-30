/-
GetElem for Mathlib Matrix so `L[i]` is a Fun row and `L[i][j]` reads an entry.
Validity is `True` (indices are typed by `m` / `n`, e.g. `Fin`).

Do not add comma GetElem sugar `L[i, j]` here: it collides with List multi-index
`term__[_,_]` from `Syntax.Data.List.List.Part8`. Use nested `L[i][j]` instead.
Distinct from Syntax ofFun sugar `[i < m, j < n] body` (has `<`).
-/
import Mathlib.LinearAlgebra.Matrix.Defs
import Notation.Fun
import Structure.Fun


namespace Matrix

variable {m n : Type*} {α : Type*}

/-- Row of a matrix as a `Fun`, so `L[i]` / `L[i][j]` work via `Fun` GetElem. -/
instance : GetElem (Matrix m n α) m (Fun n α) (fun _ _ => True) where
  getElem A i _ := ⟨A i⟩

@[simp] theorem getElem_apply (A : Matrix m n α) (i : m) :
    (A[i] : Fun n α).toFun = A i :=
  rfl

@[simp] theorem getElem_getElem (A : Matrix m n α) (i : m) (j : n) :
    A[i][j] = A i j :=
  rfl

end Matrix
