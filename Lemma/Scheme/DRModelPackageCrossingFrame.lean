import Mathlib
import Def.ModularCurve_DRResolvedModelPackageV4
import Instance.ModularCurve_DRModelPackageCrossingFrame
import Def.ModularCurve_DRModelPackageCrossingFrame

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme


theorem mem_branchIdeal_iff {X : Scheme.{u}} {ξ x : X} (h : ξ ⤳ x) (a : X.presheaf.stalk x) :
    a ∈ branchIdeal h ↔ (X.presheaf.stalkSpecializes h).hom a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) :=
  Iff.rfl

end AlgebraicGeometry.Scheme

end
