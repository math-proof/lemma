module

public import Mathlib.RingTheory.Frobenius
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

set_option autoImplicit false

namespace Matrix

variable {R : Type*} [CommRing R]


end Matrix

namespace FrobeniusDensity

open NumberField Ideal

variable (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L]


end FrobeniusDensity

namespace TaylorWiles

open NumberField Ideal FrobeniusDensity

variable {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]
variable {𝕜 : Type*} [Field 𝕜]

variable (L) in

abbrev ResidualRep (𝕜 : Type*) [Field 𝕜] := (L ≃ₐ[ℚ] L) →* Matrix (Fin 2) (Fin 2) 𝕜

variable (ρ : ResidualRep L 𝕜) (p n : ℕ)


end TaylorWiles
