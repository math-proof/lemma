/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/CarrollIdentity.lean -/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic.LinearCombination


namespace MetaMathlibExt.CarrollIdentity

open Matrix

section

variable {m : ℕ} {S : Type*} [CommRing S] (i j : Fin (m + 2))

/-- Row/column splitter for single-deletion minors. -/
def carrollSplit (p q : Fin (m + 2)) (hp : p = i ∨ p = j) (hq : q = i ∨ q = j)
    (hqp : q ≠ p) :
    Fin (m + 1) → {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} ⊕ Fin 1 :=
  fun a => if h : Fin.succAbove p a = q then Sum.inr 0
    else Sum.inl ⟨Fin.succAbove p a, by
      rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
      · exact absurd rfl hqp
      · exact ⟨Fin.succAbove_ne _ _, h⟩
      · exact ⟨h, Fin.succAbove_ne _ _⟩
      · exact absurd rfl hqp⟩

end
end MetaMathlibExt.CarrollIdentity
