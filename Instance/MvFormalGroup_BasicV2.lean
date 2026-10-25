-- Carved from Lemma/Definitions/Def_MvFormalGroup_BasicV2.lean: instance decls only.
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.CharP.Defs
import Class.MvFormalGroup_BasicV2

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace MvFormalGroup

variable {g h k : ℕ} {R : Type*} [CommRing R] {S : Type*} [CommRing S]


instance (g : ℕ) (R : Type*) [CommRing R] : IsComm (addMv g R) where
  comm := by
    intro i
    have hz : ∀ s : Fin g ⊕ Fin g, ((Sum.elim
        (fun j => (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) R))
        fun j => X (Sum.inl j)) s).constantCoeff = 0 := by
      rintro (j | j) <;> simp [constantCoeff_X]
    show subst (Sum.elim
        (fun j => (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) R))
        fun j => X (Sum.inl j))
        (X (Sum.inl i) + X (Sum.inr i)) = X (Sum.inl i) + X (Sum.inr i)
    rw [subst_X_add_X hz]
    simp only [Sum.elim_inl, Sum.elim_inr]
    exact add_comm _ _

end MvFormalGroup
end
