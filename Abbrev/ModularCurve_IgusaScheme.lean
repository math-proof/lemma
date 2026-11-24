module
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.RingTheory.Ideal.IntegralClosure
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.Polynomial.ScaleRoots
public import Mathlib.Algebra.Polynomial.Lifts
public import Structure.ModularCurve_X0
public import Def.GaloisRep_Flat
set_option autoImplicit false


public section

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
