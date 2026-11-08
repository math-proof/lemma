import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Matrix.Mul
import Notation.Fun

open Matrix

/-- Row vector on the left, Mathlib-style `ᵥ*` (`vecMul`):
`(v ᵥ* M) j = ∑ k, ↑(v k) * M k j`. -/
def Fun.vecMul {m n : ℕ} {α β : Type*} [NonUnitalNonAssocSemiring β] [Coe α β]
    (v : (Fin m) ⇀ α) (M : Matrix (Fin m) (Fin n) β) : Fin n → β :=
  Matrix.vecMul (fun k => (v.toFun k : β)) M

@[inherit_doc Fun.vecMul]
infixl:73 " ᵥ* " => Fun.vecMul

@[simp] theorem Fun.vecMul_apply {m n : ℕ} {α β : Type*} [NonUnitalNonAssocSemiring β] [Coe α β]
    (v : (Fin m) ⇀ α) (M : Matrix (Fin m) (Fin n) β) (j : Fin n) :
    (v ᵥ* M) j = ∑ k : Fin m, (v.toFun k : β) * M k j := by
  simp [Fun.vecMul, vecMul_apply_eq_sum]
