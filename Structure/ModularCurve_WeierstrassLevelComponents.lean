import Mathlib
import Structure.ModularCurve_WeierstrassLevelModuliDatum
import Instance.ModularCurve_KatzLevelP

set_option autoImplicit false

universe u

noncomputable section

open Polynomial

namespace ModularCurve

structure LevelComponent (A : Type u) [CommRing A] where

  obj : (T : Type u) → [CommRing T] → [Algebra A T] → Type u

  IsLevel : {T : Type u} → [CommRing T] → [Algebra A T] → WeierstrassCurve T → obj T → Prop

  map : {T T' : Type u} → [CommRing T] → [Algebra A T] → [CommRing T'] → [Algebra A T'] →
    (T →ₐ[A] T') → obj T → obj T'

  act : {T : Type u} → [CommRing T] → [Algebra A T] → WeierstrassCurve.VariableChange T → obj T → obj T
  map_id : ∀ {T : Type u} [CommRing T] [Algebra A T] (x : obj T), map (AlgHom.id A T) x = x
  map_comp : ∀ {T T' T'' : Type u} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] [CommRing T'']
    [Algebra A T''] (f : T →ₐ[A] T') (g : T' →ₐ[A] T'') (x : obj T), map (g.comp f) x = map g (map f x)
  act_one : ∀ {T : Type u} [CommRing T] [Algebra A T] (x : obj T), act (1 : WeierstrassCurve.VariableChange T) x = x
  act_mul : ∀ {T : Type u} [CommRing T] [Algebra A T] (C C' : WeierstrassCurve.VariableChange T) (x : obj T),
    act (C * C') x = act C (act C' x)
  map_act : ∀ {T T' : Type u} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
    (C : WeierstrassCurve.VariableChange T) (x : obj T), map f (act C x) = act (C.map f.toRingHom) (map f x)
  isLevel_map : ∀ {T T' : Type u} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
    (W : WeierstrassCurve T) (x : obj T), IsLevel W x → IsLevel (W.map f.toRingHom) (map f x)
  isLevel_act : ∀ {T : Type u} [CommRing T] [Algebra A T] (C : WeierstrassCurve.VariableChange T)
    (W : WeierstrassCurve T) (x : obj T), IsLevel W x → IsLevel (C • W) (act C x)

namespace LevelComponent

variable {A : Type u} [CommRing A]


structure Raw (L : LevelComponent A) (T : Type u) [CommRing T] [Algebra A T] : Type u where

  curve : WeierstrassCurve T

  isUnit_Δ : IsUnit curve.Δ

  level : L.obj T

  isLevel : L.IsLevel curve level


end LevelComponent

section Gamma0

variable {T : Type u} [CommRing T]


end Gamma0


section LevelP

variable {T : Type u} [CommRing T]


end LevelP


end ModularCurve

end
