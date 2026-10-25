import Mathlib
import Lemma.WeierstrassCurve.ProjModel
import Def.ModularCurve_WeierstrassLevelComponents
import Def.WeierstrassCurve_DrinfeldBasisGlobal
import Def.WeierstrassCurve_DrinfeldTransportPin
import Def.WeierstrassCurve_SectionAtOrigin
import Def.WeierstrassCurve_DrinfeldLevelFunctor

set_option autoImplicit false

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassProjModel

namespace WeierstrassCurve.DrinfeldGlobal

@[reducible] def algebraRestrict (A₀ : Type u) [CommRing A₀] (A : Type u) [CommRing A] [Algebra A₀ A]
    (T : Type u) [CommRing T] [Algebra A T] : Algebra A₀ T :=
  ((algebraMap A T).comp (algebraMap A₀ A)).toAlgebra

theorem isScalarTower_algebraRestrict (A₀ : Type u) [CommRing A₀] (A : Type u) [CommRing A] [Algebra A₀ A]
    (T : Type u) [CommRing T] [Algebra A T] :
    letI : Algebra A₀ T := algebraRestrict A₀ A T
    IsScalarTower A₀ A T :=
  letI : Algebra A₀ T := algebraRestrict A₀ A T
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

def GroupLaws.restrictScalars {A₀ : Type u} [CommRing A₀] (A : Type u) [CommRing A] [Algebra A₀ A] (𝒢₀ : GroupLaws A₀) :
    GroupLaws A :=
  fun T _ _ W hΔ =>
    letI : Algebra A₀ T := algebraRestrict A₀ A T
    𝒢₀ T W hΔ

theorem GroupLaws.restrictScalars_apply {A₀ : Type u} [CommRing A₀] (A : Type u) [CommRing A] [Algebra A₀ A] (𝒢₀ : GroupLaws A₀)
    (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (hΔ : IsUnit W.Δ) :
    𝒢₀.restrictScalars A T W hΔ = (letI : Algebra A₀ T := algebraRestrict A₀ A T; 𝒢₀ T W hΔ) :=
  rfl

def algHomRestrict (A₀ : Type u) [CommRing A₀] (A : Type u) [CommRing A] [Algebra A₀ A]
    {T T' : Type u} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T') :
    letI : Algebra A₀ T := algebraRestrict A₀ A T
    letI : Algebra A₀ T' := algebraRestrict A₀ A T'
    T →ₐ[A₀] T' :=
  letI : Algebra A₀ T := algebraRestrict A₀ A T
  letI : Algebra A₀ T' := algebraRestrict A₀ A T'
  { toRingHom := f.toRingHom
    commutes' := fun a => by
      show f (algebraMap A T (algebraMap A₀ A a)) = algebraMap A T' (algebraMap A₀ A a)
      exact f.commutes _ }

theorem algHomRestrict_toRingHom (A₀ : Type u) [CommRing A₀] (A : Type u) [CommRing A] [Algebra A₀ A]
    {T T' : Type u} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T') :
    letI : Algebra A₀ T := algebraRestrict A₀ A T
    letI : Algebra A₀ T' := algebraRestrict A₀ A T'
    (algHomRestrict A₀ A f).toRingHom = f.toRingHom :=
  rfl

theorem algHomRestrict_id (A₀ : Type u) [CommRing A₀] (A : Type u) [CommRing A] [Algebra A₀ A] (T : Type u) [CommRing T] [Algebra A T] :
    algHomRestrict A₀ A (AlgHom.id A T) = (letI : Algebra A₀ T := algebraRestrict A₀ A T; AlgHom.id A₀ T) :=
  letI : Algebra A₀ T := algebraRestrict A₀ A T
  AlgHom.ext fun _ => rfl

theorem algHomRestrict_comp (A₀ : Type u) [CommRing A₀] (A : Type u) [CommRing A] [Algebra A₀ A]
    {T T' T'' : Type u} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] [CommRing T''] [Algebra A T'']
    (f : T →ₐ[A] T') (g : T' →ₐ[A] T'') :
    algHomRestrict A₀ A (g.comp f) =
      (letI : Algebra A₀ T := algebraRestrict A₀ A T
       letI : Algebra A₀ T' := algebraRestrict A₀ A T'
       letI : Algebra A₀ T'' := algebraRestrict A₀ A T''
       (algHomRestrict A₀ A g).comp (algHomRestrict A₀ A f)) :=
  letI : Algebra A₀ T := algebraRestrict A₀ A T
  letI : Algebra A₀ T' := algebraRestrict A₀ A T'
  letI : Algebra A₀ T'' := algebraRestrict A₀ A T''
  AlgHom.ext fun _ => rfl

def LevelTransport.restrictScalars {A₀ : Type u} [CommRing A₀] (A : Type u) [CommRing A] [Algebra A₀ A]
    {𝒢₀ : GroupLaws A₀} {q : ℕ}
    (𝒯₀ : LevelTransport A₀ 𝒢₀ q) : LevelTransport A (𝒢₀.restrictScalars A) q where
  map {T T'} _ _ _ _ f x :=
    letI : Algebra A₀ T := algebraRestrict A₀ A T
    letI : Algebra A₀ T' := algebraRestrict A₀ A T'
    𝒯₀.map (algHomRestrict A₀ A f) x
  act {T} _ _ C x :=
    letI : Algebra A₀ T := algebraRestrict A₀ A T
    𝒯₀.act C x
  map_id {T} _ _ x := by
    letI : Algebra A₀ T := algebraRestrict A₀ A T
    show 𝒯₀.map (algHomRestrict A₀ A (AlgHom.id A T)) x = x
    rw [algHomRestrict_id]
    exact 𝒯₀.map_id x
  map_comp {T T' T''} _ _ _ _ _ _ f g x := by
    letI : Algebra A₀ T := algebraRestrict A₀ A T
    letI : Algebra A₀ T' := algebraRestrict A₀ A T'
    letI : Algebra A₀ T'' := algebraRestrict A₀ A T''
    show 𝒯₀.map (algHomRestrict A₀ A (g.comp f)) x = 𝒯₀.map (algHomRestrict A₀ A g) (𝒯₀.map (algHomRestrict A₀ A f) x)
    rw [algHomRestrict_comp]
    exact 𝒯₀.map_comp _ _ x
  act_one {T} _ _ x := by
    letI : Algebra A₀ T := algebraRestrict A₀ A T
    exact 𝒯₀.act_one x
  act_mul {T} _ _ C C' x := by
    letI : Algebra A₀ T := algebraRestrict A₀ A T
    exact 𝒯₀.act_mul C C' x
  map_act {T T'} _ _ _ _ f C x := by
    letI : Algebra A₀ T := algebraRestrict A₀ A T
    letI : Algebra A₀ T' := algebraRestrict A₀ A T'
    exact 𝒯₀.map_act (algHomRestrict A₀ A f) C x
  isLevel_map {T T'} _ _ _ _ f W x h := by
    letI : Algebra A₀ T := algebraRestrict A₀ A T
    letI : Algebra A₀ T' := algebraRestrict A₀ A T'
    exact 𝒯₀.isLevel_map (algHomRestrict A₀ A f) W x h
  isLevel_act {T} _ _ C W x h := by
    letI : Algebra A₀ T := algebraRestrict A₀ A T
    exact 𝒯₀.isLevel_act C W x h

theorem LevelTransport.restrictScalars_map {A₀ : Type u} [CommRing A₀] (A : Type u) [CommRing A] [Algebra A₀ A]
    {𝒢₀ : GroupLaws A₀} {q : ℕ}
    (𝒯₀ : LevelTransport A₀ 𝒢₀ q)
    {T T' : Type u} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T') (x : RawDrinfeldPair T) :
    (𝒯₀.restrictScalars A).map f x =
      (letI : Algebra A₀ T := algebraRestrict A₀ A T
       letI : Algebra A₀ T' := algebraRestrict A₀ A T'
       𝒯₀.map (algHomRestrict A₀ A f) x) :=
  rfl

theorem LevelTransport.restrictScalars_act {A₀ : Type u} [CommRing A₀] (A : Type u) [CommRing A] [Algebra A₀ A]
    {𝒢₀ : GroupLaws A₀} {q : ℕ}
    (𝒯₀ : LevelTransport A₀ 𝒢₀ q)
    {T : Type u} [CommRing T] [Algebra A T] (C : WeierstrassCurve.VariableChange T) (x : RawDrinfeldPair T) :
    (𝒯₀.restrictScalars A).act C x = (letI : Algebra A₀ T := algebraRestrict A₀ A T; 𝒯₀.act C x) :=
  rfl

end WeierstrassCurve.DrinfeldGlobal

end
