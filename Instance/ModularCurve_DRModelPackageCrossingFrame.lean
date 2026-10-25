-- Carved from Lemma/Definitions/Def_ModularCurve_DRModelPackageCrossingFrame.lean: instance decls only.
import Mathlib
import Def.ModularCurve_DRResolvedModelPackageV4
import Abbrev.ModularCurve_DRModelPackageCrossingFrame

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

instance branchIdeal_isPrime {X : Scheme.{u}} {ξ x : X} (h : ξ ⤳ x) : (branchIdeal h).IsPrime :=
  Ideal.comap_isPrime _ _

end AlgebraicGeometry.Scheme


end
