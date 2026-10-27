import Mathlib.RingTheory.Nullstellensatz
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Theorem.AlgebraicGeometry.DefinedOver
/-!
# Defined-over for affine algebraic sets

For a field `k`, the ideal of polynomials over `k` vanishing on
`Z ⊆ AlgebraicClosure k ^ n` is the comap of the Mathlib vanishing ideal
over the algebraic closure. A set is defined over `k` when its vanishing
ideal is extended from that comap ideal.
-/


noncomputable section

variable {k : Type*} [Field k]

namespace MvPolynomial

/-- `Z ⊆ AlgebraicClosure k ^ n` is defined over `k` if its vanishing ideal is
the extension of `I_k(Z)`. -/
def IsDefinedOver {n : ℕ} (Z : Set (Fin n → AlgebraicClosure k)) : Prop :=
  MvPolynomial.vanishingIdeal (AlgebraicClosure k) Z =
    Ideal.map (MvPolynomial.map (algebraMap k (AlgebraicClosure k)))
      (idealOverK Z)

end MvPolynomial
end
