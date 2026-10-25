-- Carved from Lemma/Definitions/Def_FieldTheory_RatFuncTower.lean: instance decls only.
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Algebra.Rat

set_option autoImplicit false

noncomputable section

namespace RatFuncTower

scoped instance algebraRatPoly : Algebra (Polynomial ℚ) K0 :=
  ((algebraMap (Polynomial (AlgebraicClosure ℚ)) K0).comp
    (Polynomial.mapRingHom (algebraMap ℚ (AlgebraicClosure ℚ)))).toAlgebra

end RatFuncTower

end
