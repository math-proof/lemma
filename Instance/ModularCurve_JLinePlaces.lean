module
public import Mathlib
public import Def.ModularCurve_RouteBCoordRing
public import Instance.AlgebraicCurve_RatFuncPlaces
public import Theorem.Valuation.RatFuncPlaceInfty
public import Theorem.Thm_ModularCurve_transcendental_jq
set_option autoImplicit false


public section

-- Carved from Lemma/Definitions/Def_ModularCurve_JLinePlaces.lean: instance decls only.

noncomputable section

open IntermediateField AlgebraicCurve AlgebraicCurve.RationalFunctionField

namespace ModularCurve

section Tower

variable (N : ℕ) [NeZero N]


instance instIsScalarTowerJAdjoin :
    @IsScalarTower ℚ ℚ⟮jq⟯ (modularFunctionField N)
      Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
  IsScalarTower.of_algebraMap_eq' (by apply RingHom.ext_rat)

end Tower


end ModularCurve

end
