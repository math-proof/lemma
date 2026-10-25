-- Carved from Lemma/Definitions/Def_WeierstrassCurve_ZeroComponentReduction.lean: instance decls only.
import Mathlib
import Lemma.WeierstrassCurve.ReduceHom

set_option autoImplicit false

open IsLocalRing Finset


variable {L : Type*} [Field L]


set_option autoImplicit false

namespace ModularCurve

namespace ElevenA1

open WeierstrassCurve Affine

section Count

variable {K : Type*} [CommRing K] (W : WeierstrassCurve.Affine K)

instance instDecidableEquation [DecidableEq K] (x y : K) : Decidable (W.Equation x y) :=
  decidable_of_iff _ (W.equation_iff x y).symm

instance instDecidableNonsingular [DecidableEq K] (x y : K) : Decidable (W.Nonsingular x y) :=
  decidable_of_iff _ (W.nonsingular_iff x y).symm

end Count

end ElevenA1

end ModularCurve

set_option autoImplicit false

open IsLocalRing ValuationSubring WeierstrassCurve.Affine WeierstrassCurve.Affine.Point


set_option autoImplicit false

open IsLocalRing


set_option autoImplicit false

open IsLocalRing

