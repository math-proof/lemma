import Abbrev.AlgebraicGeometry_IdealSheafModule
import Instance.AlgebraicGeometry_RelativePicardFunctor

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

noncomputable section

namespace AlgebraicGeometry

namespace Scheme.Modules

variable {X : Scheme.{u}} {M : X.Modules}

def toUnitSection (U : X.Opens) (r : Γ(X, U)) : Γ(𝟙_ X.Modules, U) := r

def ofUnitSection (U : X.Opens) (m : Γ(𝟙_ X.Modules, U)) : Γ(X, U) := m


def restrictSection (s : 𝟙_ X.Modules ⟶ M) (U : X.Opens) : Γ(M.restrict U.ι, ⊤) :=
  s.app (U.ι ''ᵁ ⊤) (toUnitSection (U.ι ''ᵁ ⊤) 1)

def coeff (s : 𝟙_ X.Modules ⟶ M) (U : X.Opens)
    (φ : M.restrict U.ι ⟶ 𝟙_ (U : Scheme.{u}).Modules) : Γ(X, U) :=
  U.topIso.hom (ofUnitSection ⊤ (φ.app ⊤ (restrictSection s U)))

def coeffIdeal (s : 𝟙_ X.Modules ⟶ M) (U : X.Opens) : Ideal Γ(X, U) :=
  Ideal.span (Set.range (coeff s U))


def zeroSchemeIdeal (s : 𝟙_ X.Modules ⟶ M) : X.IdealSheafData :=
  sInf {J : X.IdealSheafData | ∀ U : X.affineOpens, coeffIdeal s U.1 ≤ J.ideal U}


def pullbackSection {X' : Scheme.{u}} (F : X' ⟶ X) (s : 𝟙_ X.Modules ⟶ M) :
    𝟙_ X'.Modules ⟶ (Scheme.Modules.pullback F).obj M :=
  (Scheme.Modules.pullbackUnitIso F).inv ≫ (Scheme.Modules.pullback F).map s


def restrictIsoOfLE {U W : X.Opens} (h : W ≤ U)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf) :
    M.restrict W.ι ≅ 𝟙_ (W : Scheme.{u}).Modules :=
  (restrictFunctorCongr (X.homOfLE_ι h).symm).app M ≪≫
    (restrictFunctorComp (X.homOfLE h) U.ι).app M ≪≫
    (restrictFunctor (X.homOfLE h)).mapIso ((restrictFunctorIsoPullback U.ι).app M ≪≫ e) ≪≫
    (restrictFunctorIsoPullback (X.homOfLE h)).app _ ≪≫
    Scheme.Modules.pullbackUnitIso (X.homOfLE h)


def sectionDual (s : 𝟙_ X.Modules ⟶ M) : Scheme.Modules.dual M ⟶ 𝟙_ X.Modules :=
  (MonoidalClosed.pre s).app (𝟙_ X.Modules) ≫
    (MonoidalClosed.unitIsoSelf (𝟙_ X.Modules)).hom

end Scheme.Modules

def Scheme.IdealSheafData.invModuleSection {X : Scheme.{u}} (I : X.IdealSheafData) :
    𝟙_ X.Modules ⟶ I.invModule :=
  MonoidalClosed.curry' I.moduleι

end AlgebraicGeometry

end
