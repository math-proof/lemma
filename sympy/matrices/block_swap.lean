import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Block

/-! Determinant of a block matrix with a zero block on the anti-diagonal: rows split as `a ⊕ b`, columns as `b ⊕ a`; the column block swap is the rotation `finRotate^a` with sign `(-1)^(a*b)`.
-/

open Matrix Equiv

namespace Matrix.BlockSwap

/-- square view of a block matrix whose rows split as `a ⊕ b` and whose columns split as `b ⊕ a`. -/
def sq {R : Type*} {a b : ℕ} (M : Matrix (Fin a ⊕ Fin b) (Fin b ⊕ Fin a) R) : Matrix (Fin (a + b)) (Fin (a + b)) R :=
  Matrix.of fun i j => M (finSumFinEquiv.symm i) (finSumFinEquiv.symm (finCongr (Nat.add_comm a b) j))

/-- the column permutation `τ` (rotation by `a`). -/
def tau (a b : ℕ) : Perm (Fin (a + b)) :=
  ((finCongr (Nat.add_comm a b)).trans finSumFinEquiv.symm).trans ((Equiv.sumComm _ _).trans finSumFinEquiv)

end Matrix.BlockSwap
