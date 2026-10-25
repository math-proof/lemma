import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Instance.AlgebraicGeometry_IdealSheafHom

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

namespace IdealSheafData

def sres {U V : X.affineOpens} (h : V ≤ U) : Γ(X, U) →+* Γ(X, V) :=
  (X.presheaf.map (homOfLE (show (V : X.Opens) ≤ U from h)).op).hom


def resLE (I : X.IdealSheafData) {U V : X.affineOpens} (h : V ≤ U) (x : I.ideal U) :
    I.ideal V :=
  ⟨sres h (x : Γ(X, U)), I.ideal_le_comap_ideal h x.2⟩


structure IdealHom (I J : X.IdealSheafData) : Type u where

  app : ∀ U : X.affineOpens, I.ideal U →ₗ[Γ(X, U)] J.ideal U

  coe_app_resLE : ∀ {U V : X.affineOpens} (h : V ≤ U) (x : I.ideal U),
    ((app V (I.resLE h x) : J.ideal V) : Γ(X, V)) = sres h ((app U x : J.ideal U) : Γ(X, U))

namespace IdealHom

variable {I J K : X.IdealSheafData}


end IdealHom

end IdealSheafData

end AlgebraicGeometry.Scheme
