import Structure.ModularCurve_X0
import Def.ModularCurve_LaurentCoeff
import Mathlib.Algebra.Polynomial.BigOperators

set_option autoImplicit false

noncomputable section

open scoped PowerSeries.WithPiTopology
open PowerSeries HahnSeries IntermediateField Polynomial

namespace ModularCurve

section QTwist

variable {R : Type*} [CommRing R]

end QTwist

section CosetSubst

variable {K : Type*} [Field K]

end CosetSubst

section EvalAtJqN

variable (N : ℕ) [NeZero N]

end EvalAtJqN

section Symmetry

end Symmetry

section Named

variable {N : ℕ} [NeZero N]

end Named

section AdjoinRing

abbrev adjoinJq : Subalgebra ℚ (LaurentSeries ℚ) := Algebra.adjoin ℚ {jq}

end AdjoinRing

section SwapBivar

end SwapBivar

namespace PhiGen

section CosetIndex

variable (ℓ : ℕ)

end CosetIndex

section ConjugateFamily

variable {K : Type*} [Field K]

end ConjugateFamily

section Product

variable {K : Type*} [Field K] (ℓ : ℕ)

end Product

section PoleDefs

variable {K : Type*} [Field K]

end PoleDefs

section Descends

variable {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ)

end Descends

end PhiGen

end ModularCurve
