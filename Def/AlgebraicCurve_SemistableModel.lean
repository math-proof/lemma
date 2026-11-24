module
public import Mathlib
public import Lemma.ValuationSubring.SemistableCharts
public import Abbrev.AlgebraicCurve_SemistableModel
public import Instance.AlgebraicCurve_SemistableModel
set_option autoImplicit false


public section

noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing

universe u v w u₁ u₂

namespace AlgebraicCurve

namespace SemistableModel

def baseToFunctionField {R : Type u} [CommRing R] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of R)) : R →+* X.functionField :=
  (X.presheaf.germ ⊤ (genericPoint X) trivial).hom.comp
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

def localRing {F : Type v} [Field F] (X : Scheme.{u}) [IsIntegral X] (φ : F ≃+* X.functionField)
    (x : X) : Subring F :=
  ((φ.symm : X.functionField ≃+* F).toRingHom.comp
    (algebraMap (X.presheaf.stalk x) X.functionField)).range

end SemistableModel

end AlgebraicCurve

end
