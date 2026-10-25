import Mathlib
import Structure.WeierstrassCurve_ProjModel
import Structure.ModularCurve_WeierstrassLevelComponents
import Structure.WeierstrassCurve_DrinfeldBasisGlobal
import Def.WeierstrassCurve_DrinfeldTransportPin
import Def.WeierstrassCurve_SectionAtOrigin

set_option autoImplicit false

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassProjModel


namespace WeierstrassCurve.DrinfeldGlobal

variable {A : Type u} [CommRing A]

abbrev GroupLaws (A : Type u) [CommRing A] : Type (u + 1) :=
  ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T), IsUnit W.Δ →
    RelativeGroupLaw T (projModelStrCR W)


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


end WeierstrassCurve.DrinfeldGlobal

end
