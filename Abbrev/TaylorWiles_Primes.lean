import Mathlib.RingTheory.Frobenius
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

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
