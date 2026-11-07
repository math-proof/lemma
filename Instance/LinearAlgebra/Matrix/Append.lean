import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Matrix.Basic


namespace Matrix

variable {m : Type*} {a b : ℕ} {α : Type*}

/-- Append columns. `A ++ B` has `A`'s columns, then `B`'s. -/
instance : HAppend (Matrix m (Fin a) α) (Matrix m (Fin b) α) (Matrix m (Fin (a + b)) α) where
  hAppend A B := fun i => Fin.append (A i) (B i)

@[simp] theorem append_fin_apply (A : Matrix m (Fin a) α) (B : Matrix m (Fin b) α)
    (i : m) (j : Fin (a + b)) :
    (A ++ B) i j = Fin.append (A i) (B i) j :=
  rfl

theorem append_col_left (A : Matrix m (Fin a) α) (B : Matrix m (Fin b) α) (i : m) (j : Fin a) :
    (A ++ B) i (Fin.castAdd b j) = A i j := by
  rw [append_fin_apply, Fin.append_left]

theorem append_col_right (A : Matrix m (Fin a) α) (B : Matrix m (Fin b) α) (i : m) (j : Fin b) :
    (A ++ B) i (Fin.natAdd a j) = B i j := by
  rw [append_fin_apply, Fin.append_right]

/-- Append rows. `A ++ B` has `A`'s rows, then `B`'s. -/
instance {n : Type*} : HAppend (Matrix (Fin a) n α) (Matrix (Fin b) n α) (Matrix (Fin (a + b)) n α) where
  hAppend A B := Fin.append A B

theorem append_row_left {n : Type*} (A : Matrix (Fin a) n α) (B : Matrix (Fin b) n α) (i : Fin a) :
    (A ++ B) (Fin.castAdd b i) = A i :=
  Fin.append_left A B i

theorem append_row_right {n : Type*} (A : Matrix (Fin a) n α) (B : Matrix (Fin b) n α) (i : Fin b) :
    (A ++ B) (Fin.natAdd a i) = B i :=
  Fin.append_right A B i

end Matrix
