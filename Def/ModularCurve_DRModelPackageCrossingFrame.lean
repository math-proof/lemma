import Mathlib
import Def.ModularCurve_DRResolvedModelPackageV4
import Instance.ModularCurve_DRModelPackageCrossingFrame

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

def branchIdeal {X : Scheme.{u}} {ξ x : X} (h : ξ ⤳ x) : Ideal (X.presheaf.stalk x) :=
  Ideal.comap (X.presheaf.stalkSpecializes h).hom (IsLocalRing.maximalIdeal (X.presheaf.stalk ξ))

end AlgebraicGeometry.Scheme

end
