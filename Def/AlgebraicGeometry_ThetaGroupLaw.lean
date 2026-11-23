import Lemma.Scheme.ThetaGroupAction
import Def.AlgebraicGeometry_ThetaGroup
import Instance.AlgebraicGeometry_ThetaGroupLaw

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian Scheme
  TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules.fibration

variable {X : Scheme.{0}} (M : X.Modules)

def autOfIso (e : X ≅ X) (φ : (Scheme.Modules.pullback e.hom).obj M ≅ M) : Aut (RiemannForm.modulePair (A := X) M) :=
  Pseudofunctor.CoGrothendieck.isoMk (X := RiemannForm.modulePair M) (Y := RiemannForm.modulePair M) e φ.symm

def transIso (e₁ e₂ e₁₂ : X ≅ X) (h : e₁₂.hom = e₁.hom ≫ e₂.hom)
    (φ₁ : (Scheme.Modules.pullback e₁.hom).obj M ≅ M) (φ₂ : (Scheme.Modules.pullback e₂.hom).obj M ≅ M) :
    (Scheme.Modules.pullback e₁₂.hom).obj M ≅ M :=
  (pullbackCongr h).app M ≪≫ ((pullbackComp e₁.hom e₂.hom).app M).symm ≪≫
    (Scheme.Modules.pullback e₁.hom).mapIso φ₂ ≪≫ φ₁

def reflIso (e : X ≅ X) (h : e.hom = 𝟙 X) : (Scheme.Modules.pullback e.hom).obj M ≅ M :=
  (pullbackCongr h).app M ≪≫ (pullbackId X).app M

def symmIso (e e' : X ≅ X) (h : e'.hom ≫ e.hom = 𝟙 X) (φ : (Scheme.Modules.pullback e.hom).obj M ≅ M) :
    (Scheme.Modules.pullback e'.hom).obj M ≅ M :=
  ((Scheme.Modules.pullback e'.hom).mapIso φ).symm ≪≫ (pullbackComp e'.hom e.hom).app M ≪≫
    (pullbackCongr h).app M ≪≫ (pullbackId X).app M

end AlgebraicGeometry.Scheme.Modules.fibration

namespace AlgebraicGeometry.Scheme.Modules

section Homothety

variable {Y : Scheme.{0}} (N : Y.Modules)

def topRes (r : Γ(Y, ⊤)) (U : Y.Opens) : Γ(Y, U) := Y.presheaf.map (homOfLE (le_top (a := U))).op r

def homothety (r : Γ(Y, ⊤)) : N ⟶ N :=
  ⟨PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom
        (DistribSMul.toAddMonoidHom Γ(N, U.unop) (topRes r U.unop))
      naturality := fun {U V} i => by
        obtain ⟨i⟩ := i
        ext s
        change topRes r (unop V) • (show Γ(N, unop V) from N.presheaf.map i.op s) =
          N.presheaf.map i.op (topRes r (unop U) • (show Γ(N, unop U) from s))
        rw [Scheme.Modules.map_smul, map_topRes] }
    (fun U a m => by
      change topRes r U.unop • ((show Γ(Y, U.unop) from a) • m) = (show Γ(Y, U.unop) from a) • (topRes r U.unop • m)
      exact smul_comm _ _ _)⟩

def homothetyIso (u : Γ(Y, ⊤)ˣ) : N ≅ N where
  hom := homothety N (u : Γ(Y, ⊤))
  inv := homothety N (u⁻¹ : Γ(Y, ⊤)ˣ)
  hom_inv_id := by rw [← homothety_mul, Units.inv_mul, homothety_one]
  inv_hom_id := by rw [← homothety_mul, Units.mul_inv, homothety_one]

end Homothety

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Polarisation

set_option linter.unusedVariables false in

def PtGrp {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) : Type := SchemeHomOver t f

variable {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
variable {R : Type} [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))

def prPt : SchemeHomOver (pullback.snd f t ≫ t) f := ⟨pullback.fst f t, pullback.condition⟩

def constPtR (x : SchemeHomOver t f) : SchemeHomOver (pullback.snd f t ≫ t) f :=
  schemeHomOverComp (pullback.snd f t) rfl x

def translateIso (x : SchemeHomOver t f) : pullback f t ≅ pullback f t where
  hom := translate f L t x
  inv := translate f L t (L.inv t x)
  hom_inv_id := translate_mul_inv f L t x
  inv_hom_id := translate_inv_mul f L t x

def baseScalarHom : R →+* Γ(pullback f t, ⊤) :=
  (pullback.snd f t).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

namespace ThetaPt

variable {f} {L} {𝓛 : A.Modules} {t}

def mul (θ θ' : ThetaPt f L 𝓛 t) : ThetaPt f L 𝓛 t where
  pt := L.mul t θ.pt θ'.pt
  iso := Scheme.Modules.fibration.transIso _ (translateIso f L t θ.pt) (translateIso f L t θ'.pt) (translateIso f L t (L.mul t θ.pt θ'.pt))
    (translate_mul f L t θ.pt θ'.pt) θ.iso θ'.iso

def one : ThetaPt f L 𝓛 t where
  pt := L.one t
  iso := Scheme.Modules.fibration.reflIso _ (translateIso f L t (L.one t)) (translate_one f L t)

def inv (θ : ThetaPt f L 𝓛 t) : ThetaPt f L 𝓛 t where
  pt := L.inv t θ.pt
  iso := Scheme.Modules.fibration.symmIso _ (translateIso f L t θ.pt) (translateIso f L t (L.inv t θ.pt)) (translate_inv_mul f L t θ.pt) θ.iso

def ofUnit (u : Γ(pullback f t, ⊤)ˣ) : ThetaPt f L 𝓛 t where
  pt := L.one t
  iso := Scheme.Modules.fibration.reflIso _ (translateIso f L t (L.one t)) (translate_one f L t) ≪≫ Scheme.Modules.homothetyIso _ u

def ofScalar (c : Rˣ) : ThetaPt f L 𝓛 t := ofUnit (Units.map (baseScalarHom f t).toMonoidHom c)

def toAut (θ : ThetaPt f L 𝓛 t) :
    Aut (RiemannForm.modulePair (A := pullback f t) ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛)) :=
  Scheme.Modules.fibration.autOfIso _ (translateIso f L t θ.pt) θ.iso

def toGrp (θ : ThetaPt f L 𝓛 t) :
    (Aut (RiemannForm.modulePair (A := pullback f t) ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛)))ᵐᵒᵖ ×
      PtGrp L t :=
  (MulOpposite.op (toAut θ), θ.pt)

def toGrpHom : ThetaPt f L 𝓛 t →* (Aut (RiemannForm.modulePair (A := pullback f t)
      ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛)))ᵐᵒᵖ × PtGrp L t where
  toFun := toGrp
  map_one' := toGrp_one
  map_mul' := toGrp_mul

def ptHom : ThetaPt f L 𝓛 t →* PtGrp L t := (MonoidHom.snd _ _).comp toGrpHom

def thetaGroupR : Subgroup ((Aut (RiemannForm.modulePair (A := pullback f t)
      ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛)))ᵐᵒᵖ × PtGrp L t) :=
  (toGrpHom (f := f) (L := L) (𝓛 := 𝓛) (t := t)).range

def equivThetaGroupR : ThetaPt f L 𝓛 t ≃* thetaGroupR (f := f) (L := L) (𝓛 := 𝓛) (t := t) :=
  MonoidHom.ofInjective toGrp_injective

end ThetaPt

end AlgebraicGeometry.Polarisation

end
