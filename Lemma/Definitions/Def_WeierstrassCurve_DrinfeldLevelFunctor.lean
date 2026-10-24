import Mathlib
import Lemma.Definitions.Def_WeierstrassCurve_ProjModel
import Lemma.Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Lemma.Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Lemma.Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Lemma.Definitions.Def_WeierstrassCurve_SectionAtOrigin

set_option autoImplicit false

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassProjModel

attribute [local instance] MvPolynomial.gradedAlgebra

namespace WeierstrassCurve.DrinfeldGlobal

variable {A : Type u} [CommRing A]

abbrev GroupLaws (A : Type u) [CommRing A] : Type (u + 1) :=
  ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T), IsUnit W.Δ →
    RelativeGroupLaw T (projModelStrCR W)

def GroupLaws.IsChordTangent (𝒢 : GroupLaws A) : Prop :=
  ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (hΔ : IsUnit W.Δ),
    ∃ ev, IsPointsEval W (𝒢 T W hΔ) ev

def GroupLaws.IsOriginIdentity (𝒢 : GroupLaws A) : Prop :=
  ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (hΔ : IsUnit W.Δ),
    ∃ χ : OriginChartRing W →+* T,
      IsOriginChartSection ((𝒢 T W hΔ).one (𝟙 _)) χ ∧ χ (xOverY W) = 0 ∧ χ (zOverY W) = 0

def RawDrinfeldPair.IsLevel (𝒢 : GroupLaws A) (q : ℕ)
    {T : Type u} [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (x : RawDrinfeldPair T) : Prop :=
  x.curve = W ∧ ∃ hΔ : IsUnit x.curve.Δ, IsDrinfeldBasis (𝒢 T x.curve hΔ) q x.P x.Q

structure LevelTransport (A : Type u) [CommRing A] (𝒢 : GroupLaws A) (q : ℕ) where
  map : {T T' : Type u} → [CommRing T] → [Algebra A T] → [CommRing T'] → [Algebra A T'] →
    (T →ₐ[A] T') → RawDrinfeldPair T → RawDrinfeldPair T'
  act : {T : Type u} → [CommRing T] → [Algebra A T] →
    WeierstrassCurve.VariableChange T → RawDrinfeldPair T → RawDrinfeldPair T
  map_id : ∀ {T : Type u} [CommRing T] [Algebra A T] (x : RawDrinfeldPair T), map (AlgHom.id A T) x = x
  map_comp : ∀ {T T' T'' : Type u} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] [CommRing T'']
    [Algebra A T''] (f : T →ₐ[A] T') (g : T' →ₐ[A] T'') (x : RawDrinfeldPair T),
    map (g.comp f) x = map g (map f x)
  act_one : ∀ {T : Type u} [CommRing T] [Algebra A T] (x : RawDrinfeldPair T),
    act (1 : WeierstrassCurve.VariableChange T) x = x
  act_mul : ∀ {T : Type u} [CommRing T] [Algebra A T] (C C' : WeierstrassCurve.VariableChange T)
    (x : RawDrinfeldPair T), act (C * C') x = act C (act C' x)
  map_act : ∀ {T T' : Type u} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
    (C : WeierstrassCurve.VariableChange T) (x : RawDrinfeldPair T),
    map f (act C x) = act (C.map f.toRingHom) (map f x)
  isLevel_map : ∀ {T T' : Type u} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
    (W : WeierstrassCurve T) (x : RawDrinfeldPair T),
    RawDrinfeldPair.IsLevel 𝒢 q W x → RawDrinfeldPair.IsLevel 𝒢 q (W.map f.toRingHom) (map f x)
  isLevel_act : ∀ {T : Type u} [CommRing T] [Algebra A T] (C : WeierstrassCurve.VariableChange T)
    (W : WeierstrassCurve T) (x : RawDrinfeldPair T),
    RawDrinfeldPair.IsLevel 𝒢 q W x → RawDrinfeldPair.IsLevel 𝒢 q (C • W) (act C x)

def LevelTransport.IsSectionTransport {𝒢 : GroupLaws A} {q : ℕ} (𝒯 : LevelTransport A 𝒢 q) : Prop :=
  (∀ (T : Type u) [CommRing T] [Algebra A T] (C : WeierstrassCurve.VariableChange T) (x : RawDrinfeldPair T),
    ∃ hc : (𝒯.act C x).curve = C • x.curve,
      ∀ (φ : projModelGradingCR x.curve →+*ᵍ projModelGradingCR (C • x.curve))
        (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • x.curve)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR x.curve)).map φ),
        IsVariableChangeHom x.curve C φ →
          (𝒯.act C x).P.1 ≫ eqToHom (congrArg projModelCR hc) ≫ Proj.map φ hφ = x.P.1 ∧
          (𝒯.act C x).Q.1 ≫ eqToHom (congrArg projModelCR hc) ≫ Proj.map φ hφ = x.Q.1) ∧
  (∀ (T T' : Type u) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
    (x : RawDrinfeldPair T),
    ∃ hc : (𝒯.map f x).curve = x.curve.map f.toRingHom,
      ∀ (φ : projModelGradingCR x.curve →+*ᵍ projModelGradingCR (x.curve.map f.toRingHom))
        (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (x.curve.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR x.curve)).map φ),
        IsCoefficientHom x.curve f.toRingHom φ →
          (𝒯.map f x).P.1 ≫ eqToHom (congrArg projModelCR hc) ≫ Proj.map φ hφ =
            Spec.map (CommRingCat.ofHom f.toRingHom) ≫ x.P.1 ∧
          (𝒯.map f x).Q.1 ≫ eqToHom (congrArg projModelCR hc) ≫ Proj.map φ hφ =
            Spec.map (CommRingCat.ofHom f.toRingHom) ≫ x.Q.1)

def levelComponent (A : Type u) [CommRing A] (𝒢 : GroupLaws A) (q : ℕ) (𝒯 : LevelTransport A 𝒢 q) :
    ModularCurve.LevelComponent A where
  obj T _ _ := RawDrinfeldPair T
  IsLevel W x := RawDrinfeldPair.IsLevel 𝒢 q W x
  map f x := 𝒯.map f x
  act C x := 𝒯.act C x
  map_id x := 𝒯.map_id x
  map_comp f g x := 𝒯.map_comp f g x
  act_one x := 𝒯.act_one x
  act_mul C C' x := 𝒯.act_mul C C' x
  map_act f C x := 𝒯.map_act f C x
  isLevel_map f W x h := 𝒯.isLevel_map f W x h
  isLevel_act C W x h := 𝒯.isLevel_act C W x h

def rigidData (A : Type u) [CommRing A] (ℓ N q : ℕ)
    (hℓ : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hN : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (h : Polynomial T), W.IsCyclicKernel N h → (C • W).IsCyclicKernel N (ModularCurve.kernelVariableChangeDeg C ((N - 1) / 2) h))
    (𝒢 : GroupLaws A) (𝒯 : LevelTransport A 𝒢 q) : ModularCurve.RigidWeierstrassData.{u} A :=
  ModularCurve.weierstrassLevelRigidData A ℓ N hℓ hN (levelComponent A 𝒢 q 𝒯)

end WeierstrassCurve.DrinfeldGlobal

end
