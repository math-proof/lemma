-- Carved from Lemma/Definitions/Def_FieldTheory_RatFuncTower.lean: instance decls only.

module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Algebra.Rat

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace RatFuncTower

scoped instance algebraRatPoly : Algebra (Polynomial ℚ) K0 :=
  ((algebraMap (Polynomial (AlgebraicClosure ℚ)) K0).comp
    (Polynomial.mapRingHom (algebraMap ℚ (AlgebraicClosure ℚ)))).toAlgebra

end RatFuncTower

end
