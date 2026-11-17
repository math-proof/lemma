module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.Valuation.Discrete.Basic
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Ring.Subring.Pointwise
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Bezout
public import Structure.AlgebraicCurve_Place

set_option autoImplicit false

@[expose] public noncomputable section

open IsDedekindDomain WithZero IsLocalRing

namespace AlgebraicCurve

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

abbrev Divisor : Type _ := Place K F →₀ ℤ

namespace Divisor

variable {K F}

end Divisor


namespace Place

open scoped Pointwise

variable {K F}
variable (σ : F ≃ₐ[K] F)

end Place

namespace Divisor

open scoped Pointwise

variable {K F}

end Divisor


namespace Place

variable {K F}
variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]

end Place

end AlgebraicCurve
