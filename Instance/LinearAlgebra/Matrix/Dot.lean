import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Matrix.Mul
import Notation.Data.Fin.Dot
import Structure.Fun


/-- Row vector on the left: `(v @ M) i j = ∑ k, v k * M k j`. -/
instance {m n : ℕ} {α β : Type*} [Mul β] [AddCommMonoid β] [Coe α β] :
    Dot (Fun (Fin m) α) (Matrix (Fin m) (Fin n) β) (Matrix (Fin 1) (Fin n) β) where
  dot v M := Matrix.of fun (_ : Fin 1) j => ∑ k : Fin m, (v.toFun k : β) * M k j

@[simp] theorem Fun.dot_matrix_apply {m n : ℕ} {α β : Type*} [Mul β] [AddCommMonoid β] [Coe α β]
    (v : Fun (Fin m) α) (M : Matrix (Fin m) (Fin n) β) (i : Fin 1) (j : Fin n) :
    (v @ M) i j = ∑ k : Fin m, (v.toFun k : β) * M k j :=
  rfl
