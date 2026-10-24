import Lemma.Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Lemma.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

noncomputable section

namespace AlgebraicGeometry

namespace Scheme.Modules

variable {X : Scheme.{u}} {M : X.Modules}

def toUnitSection (U : X.Opens) (r : Γ(X, U)) : Γ(𝟙_ X.Modules, U) := r

def ofUnitSection (U : X.Opens) (m : Γ(𝟙_ X.Modules, U)) : Γ(X, U) := m

@[simp] lemma ofUnitSection_toUnitSection (U : X.Opens) (r : Γ(X, U)) :
    ofUnitSection U (toUnitSection U r) = r := rfl

@[simp] lemma toUnitSection_ofUnitSection (U : X.Opens) (m : Γ(𝟙_ X.Modules, U)) :
    toUnitSection U (ofUnitSection U m) = m := rfl

lemma ofUnitSection_injective (U : X.Opens) : Function.Injective (ofUnitSection (X := X) U) :=
  fun _ _ h => h

lemma ofUnitSection_map {U V : X.Opens} (i : V ⟶ U) (m : Γ(𝟙_ X.Modules, U)) :
    ofUnitSection V ((𝟙_ X.Modules).presheaf.map i.op m) =
      X.presheaf.map i.op (ofUnitSection U m) := rfl

lemma ofUnitSection_smul (U : X.Opens) (r : Γ(X, U)) (m : Γ(𝟙_ X.Modules, U)) :
    ofUnitSection U (r • m) = r * ofUnitSection U m := rfl

def restrictSection (s : 𝟙_ X.Modules ⟶ M) (U : X.Opens) : Γ(M.restrict U.ι, ⊤) :=
  s.app (U.ι ''ᵁ ⊤) (toUnitSection (U.ι ''ᵁ ⊤) 1)

def coeff (s : 𝟙_ X.Modules ⟶ M) (U : X.Opens)
    (φ : M.restrict U.ι ⟶ 𝟙_ (U : Scheme.{u}).Modules) : Γ(X, U) :=
  U.topIso.hom (ofUnitSection ⊤ (φ.app ⊤ (restrictSection s U)))

def coeffIdeal (s : 𝟙_ X.Modules ⟶ M) (U : X.Opens) : Ideal Γ(X, U) :=
  Ideal.span (Set.range (coeff s U))

lemma coeff_mem_coeffIdeal (s : 𝟙_ X.Modules ⟶ M) (U : X.Opens)
    (φ : M.restrict U.ι ⟶ 𝟙_ (U : Scheme.{u}).Modules) : coeff s U φ ∈ coeffIdeal s U :=
  Ideal.subset_span ⟨φ, rfl⟩

def zeroSchemeIdeal (s : 𝟙_ X.Modules ⟶ M) : X.IdealSheafData :=
  sInf {J : X.IdealSheafData | ∀ U : X.affineOpens, coeffIdeal s U.1 ≤ J.ideal U}

abbrev zeroScheme (s : 𝟙_ X.Modules ⟶ M) : Scheme.{u} :=
  (zeroSchemeIdeal s).subscheme

lemma zeroSchemeIdeal_le {s : 𝟙_ X.Modules ⟶ M} {J : X.IdealSheafData}
    (h : ∀ U : X.affineOpens, coeffIdeal s U.1 ≤ J.ideal U) : zeroSchemeIdeal s ≤ J :=
  sInf_le h

lemma le_zeroSchemeIdeal {s : 𝟙_ X.Modules ⟶ M} {K : X.IdealSheafData}
    (h : ∀ J : X.IdealSheafData, (∀ U : X.affineOpens, coeffIdeal s U.1 ≤ J.ideal U) → K ≤ J) :
    K ≤ zeroSchemeIdeal s :=
  le_sInf fun _ hJ => h _ hJ

lemma zeroSchemeIdeal_eq_of_isLeast {s : 𝟙_ X.Modules ⟶ M} {P : X.IdealSheafData}
    (hP : IsLeast {J : X.IdealSheafData | ∀ U : X.affineOpens, coeffIdeal s U.1 ≤ J.ideal U} P) :
    zeroSchemeIdeal s = P :=
  hP.isGLB.sInf_eq

def pullbackSection {X' : Scheme.{u}} (F : X' ⟶ X) (s : 𝟙_ X.Modules ⟶ M) :
    𝟙_ X'.Modules ⟶ (Scheme.Modules.pullback F).obj M :=
  (Scheme.Modules.pullbackUnitIso F).inv ≫ (Scheme.Modules.pullback F).map s

@[simp] lemma pullbackSection_def {X' : Scheme.{u}} (F : X' ⟶ X) (s : 𝟙_ X.Modules ⟶ M) :
    pullbackSection F s =
      (Scheme.Modules.pullbackUnitIso F).inv ≫ (Scheme.Modules.pullback F).map s :=
  rfl

def restrictIsoOfLE {U W : X.Opens} (h : W ≤ U)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf) :
    M.restrict W.ι ≅ 𝟙_ (W : Scheme.{u}).Modules :=
  (restrictFunctorCongr (X.homOfLE_ι h).symm).app M ≪≫
    (restrictFunctorComp (X.homOfLE h) U.ι).app M ≪≫
    (restrictFunctor (X.homOfLE h)).mapIso ((restrictFunctorIsoPullback U.ι).app M ≪≫ e) ≪≫
    (restrictFunctorIsoPullback (X.homOfLE h)).app _ ≪≫
    Scheme.Modules.pullbackUnitIso (X.homOfLE h)

theorem IsInvertible.exists_restrict_iso (hM : Scheme.Modules.IsInvertible M) {V : X.Opens} {x : X}
    (hx : x ∈ V) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧ U.1 ≤ V ∧
      Nonempty (M.restrict U.1.ι ≅ 𝟙_ (U.1 : Scheme.{u}).Modules) := by
  obtain ⟨U₀, hxU₀, ⟨e⟩⟩ := hM.exists_trivialization x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUle⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ V ⊓ U₀ from ⟨hx, hxU₀⟩)
      (V ⊓ U₀).isOpen
  exact ⟨⟨U, hU⟩, hxU, fun y hy => (hUle hy).1, ⟨restrictIsoOfLE (fun y hy => (hUle hy).2) e⟩⟩

def sectionDual (s : 𝟙_ X.Modules ⟶ M) : Scheme.Modules.dual M ⟶ 𝟙_ X.Modules :=
  (MonoidalClosed.pre s).app (𝟙_ X.Modules) ≫
    (MonoidalClosed.unitIsoSelf (𝟙_ X.Modules)).hom

end Scheme.Modules

def Scheme.IdealSheafData.invModuleSection {X : Scheme.{u}} (I : X.IdealSheafData) :
    𝟙_ X.Modules ⟶ I.invModule :=
  MonoidalClosed.curry' I.moduleι

end AlgebraicGeometry

end
