import Class.AlgebraicCurve_DivisorPushPull
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.Algebra.Polynomial.Lifts

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero IsLocalRing

namespace AlgebraicCurve

namespace Place

section SinglePlace

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

end SinglePlace

section IntegrallyClosed

open Polynomial

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)

end IntegrallyClosed

section Chart

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
variable (w : Place K F)

end Chart

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']

section Setup

variable (v : Place K F)

variable (F') in

abbrev integralClosureAt : Type _ := integralClosure v.toValuationSubring F'

omit [Algebra K F'] [IsScalarTower K F F'] [FiniteDimensional F F']
  [Algebra.IsSeparable F F'] in

end Setup

section Center

variable {v : Place K F} {w : Place K F'}

end Center

section Bijection

variable {v : Place K F}

end Bijection

section Fiber

variable (v : Place K F)

end Fiber

end Place

end AlgebraicCurve

end
