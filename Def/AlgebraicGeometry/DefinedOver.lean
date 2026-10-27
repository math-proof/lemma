import Mathlib.RingTheory.Nullstellensatz
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
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

/-- The ideal `I_k(Z) ⊆ k[X]` of polynomials over `k` vanishing on `Z`,
obtained by pulling back the vanishing ideal over the algebraic closure. -/
noncomputable def idealOverK {n : ℕ} (Z : Set (Fin n → AlgebraicClosure k)) :
    Ideal (MvPolynomial (Fin n) k) :=
  Ideal.comap (MvPolynomial.map (algebraMap k (AlgebraicClosure k)))
    (MvPolynomial.vanishingIdeal (AlgebraicClosure k) Z)

end MvPolynomial
end
