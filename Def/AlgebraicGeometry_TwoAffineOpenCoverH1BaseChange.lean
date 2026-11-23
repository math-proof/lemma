import Lemma.Scheme.RelPicardStageHom
import Structure.AlgebraicGeometry_TwoAffineOpenCoverH1BaseChange

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite NeronModelInfra

namespace AlgebraicGeometry.Scheme.TwoAffineOpenCover

variable {R : Type u} [CommRing R] {S : Type u} [CommRing S] {T : Type u} [CommRing T]


namespace HomOver

variable {τ : R →+* S} {X : Scheme.{u}} {𝒱 : X.TwoAffineOpenCover} {c : X ⟶ Spec (.of R)}
  {Y : Scheme.{u}} {𝒲 : Y.TwoAffineOpenCover} {c' : Y ⟶ Spec (.of S)} (f : HomOver τ 𝒱 c 𝒲 c')

def sectionsMap {U : X.Opens} {V : Y.Opens} (h : V ≤ f.hom ⁻¹ᵁ U) :
    letI := algebraOfHom c U; letI := algebraOfHom c' V
    Γ(X, U) →ₛₗ[τ] Γ(Y, V) :=
  letI := algebraOfHom c U; letI := algebraOfHom c' V
  { toFun := (f.hom.appLE U V h).hom
    map_add' := fun x y => map_add _ x y
    map_smul' := fun r x => by
      change (f.hom.appLE U V h).hom ((algebraOfHom c U).algebraMap r * x) =
        (algebraOfHom c' V).algebraMap (τ r) * (f.hom.appLE U V h).hom x
      rw [map_mul, appLE_algebraMap] }

def map0 : (𝒱.cover c).A0 →ₛₗ[τ] (𝒲.cover c').A0 := f.sectionsMap f.U0_le

def map1 : (𝒱.cover c).A1 →ₛₗ[τ] (𝒲.cover c').A1 := f.sectionsMap f.U1_le

def map01 : (𝒱.cover c).A01 →ₛₗ[τ] (𝒲.cover c').A01 := f.sectionsMap f.inf_le

def H1map : (𝒱.structureSheafSections c).H1 →ₛₗ[τ] (𝒲.structureSheafSections c').H1 :=
  Submodule.mapQ _ _ f.map01 f.range_cechDiff_le_comap

protected def id (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R)) : HomOver (RingHom.id R) 𝒱 c 𝒱 c where
  hom := 𝟙 X
  comm := by
    change 𝟙 X ≫ c = c ≫ Spec.map (𝟙 _)
    rw [Spec.map_id, Category.id_comp, Category.comp_id]
  U0_le := le_rfl
  U1_le := le_rfl

def comp {υ : S →+* T} {Z : Scheme.{u}} {𝒳 : Z.TwoAffineOpenCover} {c'' : Z ⟶ Spec (.of T)}
    (g : HomOver υ 𝒲 c' 𝒳 c'') (f : HomOver τ 𝒱 c 𝒲 c') : HomOver (υ.comp τ) 𝒱 c 𝒳 c'' where
  hom := g.hom ≫ f.hom
  comm := by
    rw [Category.assoc, f.comm, ← Category.assoc, g.comm, Category.assoc, ← Spec.map_comp]
    rfl
  U0_le := g.U0_le.trans (by rw [Scheme.Hom.comp_preimage]; exact Scheme.Hom.preimage_mono _ f.U0_le)
  U1_le := g.U1_le.trans (by rw [Scheme.Hom.comp_preimage]; exact Scheme.Hom.preimage_mono _ f.U1_le)

end HomOver

section BaseChange

variable {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
  {A : Type u} [CommRing A] [Algebra R A] {B : Type u} [CommRing B] [Algebra R B]
  {B' : Type u} [CommRing B'] [Algebra R B']

variable (A) in

def HomOver.baseChange :
    HomOver (algebraMap R A) 𝒱 c (𝒱.pullback c A) (pullback.snd c (specMap R A)) where
  hom := pullback.fst c (specMap R A)
  comm := pullback.condition
  U0_le := le_rfl
  U1_le := le_rfl

def HomOver.stage (g : A →ₐ[R] B) :
    HomOver g.toRingHom (𝒱.pullback c A) (pullback.snd c (specMap R A))
      (𝒱.pullback c B) (pullback.snd c (specMap R B)) where
  hom := RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R g)
  comm := pullback.lift_snd _ _ _
  U0_le := (baseChangeSnd_preimage_U0 𝒱 c (RelPicard.LFP.stageHom R g)).ge
  U1_le := (baseChangeSnd_preimage_U1 𝒱 c (RelPicard.LFP.stageHom R g)).ge

variable (A) in

def H1baseChangeMap : (𝒱.structureSheafSections c).H1 →ₛₗ[algebraMap R A]
    ((𝒱.pullback c A).structureSheafSections (pullback.snd c (specMap R A))).H1 :=
  (HomOver.baseChange 𝒱 c A).H1map

def H1stageMap (g : A →ₐ[R] B) :
    ((𝒱.pullback c A).structureSheafSections (pullback.snd c (specMap R A))).H1 →ₛₗ[g.toRingHom]
      ((𝒱.pullback c B).structureSheafSections (pullback.snd c (specMap R B))).H1 :=
  (HomOver.stage 𝒱 c g).H1map

end BaseChange

end AlgebraicGeometry.Scheme.TwoAffineOpenCover

end
