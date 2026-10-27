import Mathlib.RingTheory.Nullstellensatz
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Def.AlgebraicGeometry.DefinedOver
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

/-- `f ∈ I_k(Z)` iff its image in `AlgebraicClosure k[X]` vanishes on `Z`. -/
theorem mem_idealOverK_iff {n : ℕ} {Z : Set (Fin n → AlgebraicClosure k)}
    {f : MvPolynomial (Fin n) k} :
    f ∈ idealOverK Z ↔
      MvPolynomial.map (algebraMap k (AlgebraicClosure k)) f ∈
        MvPolynomial.vanishingIdeal (AlgebraicClosure k) Z := by
  rfl

end MvPolynomial
end
