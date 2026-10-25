import Mathlib
import Abbrev.MvPolynomial_CrossingResolution
import Inductive.MvPolynomial_GlueIndex

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace MvPolynomial

namespace CrossingQuotient

variable {W : Type u} [CommRing W] (t : W)

abbrev OverlapRing : Type u := Localization.Away (V t)

abbrev TorusRing : Type u :=
  Localization.Away (algebraMap (CrossingQuotient W t) (OverlapRing t) (U t))

abbrev xT : TorusRing t := algebraMap (CrossingQuotient W t) (TorusRing t) (U t)

abbrev yT : TorusRing t := algebraMap (CrossingQuotient W t) (TorusRing t) (V t)

abbrev tT : TorusRing t := algebraMap W (TorusRing t) t

abbrev tinv : TorusRing t :=
  IsLocalization.Away.invSelf (S := TorusRing t) (algebraMap W (CrossingQuotient W t) t)

section transition

end transition

section spectra

abbrev crossingScheme (s : W) : Scheme.{u} := Spec (CommRingCat.of (CrossingQuotient W s))

abbrev chartScheme : Scheme.{u} := crossingScheme t

abbrev overlapScheme : Scheme.{u} := Spec (CommRingCat.of (OverlapRing t))

abbrev torusScheme : Scheme.{u} := Spec (CommRingCat.of (TorusRing t))

abbrev overlapToChartLeft : overlapScheme t ⟶ chartScheme t :=
  Spec.map (CommRingCat.ofHom (algebraMap (CrossingQuotient W t) (OverlapRing t)))

abbrev overlapToChartRight : overlapScheme t ⟶ chartScheme t :=
  Spec.map (CommRingCat.ofHom (transitionUp t).toRingHom)

end spectra

namespace GlueIndex

variable {e : ℕ}

end GlueIndex

open GlueIndex

section diagram

variable (e : ℕ)

end diagram

section locallyDirected

variable (e : ℕ)

end locallyDirected

section scheme

variable (e : ℕ)


end scheme

end CrossingQuotient

end MvPolynomial

end
