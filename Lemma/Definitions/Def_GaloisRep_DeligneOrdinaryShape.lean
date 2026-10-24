import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Algebra.Group.Subgroup.Basic

set_option autoImplicit false

namespace GaloisRep

section Shapes

variable {A : Type*} [CommRing A] {H : Type*} [Group H]

open Matrix

def DeligneOrdinaryShape (ρloc : H →* GL (Fin 2) A) (I : Subgroup H) (frob : H)
    (χ : H →* A) (k : ℕ) (ap εp : A) : Prop :=
  ∃ g : GL (Fin 2) A,
    (∀ σ : H, (g * ρloc σ * g⁻¹).val 1 0 = 0) ∧
    (∀ σ ∈ I, (g * ρloc σ * g⁻¹).val 1 1 = 1) ∧
    (g * ρloc frob * g⁻¹).val 1 1 = ap ∧
    (∀ σ ∈ I, (g * ρloc σ * g⁻¹).val 0 0 = χ σ ^ (k - 1)) ∧
    ap * (g * ρloc frob * g⁻¹).val 0 0 = χ frob ^ (k - 1) * εp

end Shapes

end GaloisRep
