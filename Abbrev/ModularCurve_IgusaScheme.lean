import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Mathlib.Algebra.Polynomial.Lifts
import Structure.ModularCurve_X0
import Def.GaloisRep_Flat

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial

namespace ModularCurve

namespace IgusaScheme

variable (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]

scoped instance igusaAlgebra :
    Algebra ↥(GaloisRep.ratLocalizedAt ℓ) ↥(modularFunctionFieldFull N) :=
  ((algebraMap ℚ ↥(modularFunctionFieldFull N)).comp
    (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ)).toAlgebra

scoped instance igusaScalarTower :
    IsScalarTower ↥(GaloisRep.ratLocalizedAt ℓ) ℚ ↥(modularFunctionFieldFull N) :=
  IsScalarTower.of_algebraMap_eq' rfl

end IgusaScheme

end ModularCurve

end
