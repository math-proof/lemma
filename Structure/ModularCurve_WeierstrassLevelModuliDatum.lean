import Mathlib
import Instance.ModularCurve_LevelModuliPackage
import Structure.ModularCurve_WeierstrassLevelCarrier

set_option autoImplicit false

universe u

namespace ModularCurve

structure RigidWeierstrassData (A : Type u) [CommRing A] where

  Raw : (T : Type u) → [CommRing T] → [Algebra A T] → Type u

  curve : {T : Type u} → [CommRing T] → [Algebra A T] → Raw T → WeierstrassCurve T

  isUnit_Δ : ∀ {T : Type u} [CommRing T] [Algebra A T] (x : Raw T), IsUnit (curve x).Δ

  mapRing : {T T' : Type u} → [CommRing T] → [Algebra A T] → [CommRing T'] → [Algebra A T'] →
    (T →ₐ[A] T') → Raw T → Raw T'

  curve_mapRing : ∀ {T T' : Type u} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
    (x : Raw T), curve (mapRing f x) = (curve x).map f.toRingHom

  mapRing_id : ∀ {T : Type u} [CommRing T] [Algebra A T] (x : Raw T), mapRing (AlgHom.id A T) x = x

  mapRing_comp : ∀ {T T' T'' : Type u} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] [CommRing T'']
    [Algebra A T''] (f : T →ₐ[A] T') (g : T' →ₐ[A] T'') (x : Raw T), mapRing (g.comp f) x = mapRing g (mapRing f x)

  act : {T : Type u} → [CommRing T] → [Algebra A T] → WeierstrassCurve.VariableChange T → Raw T → Raw T

  act_one : ∀ {T : Type u} [CommRing T] [Algebra A T] (x : Raw T), act (1 : WeierstrassCurve.VariableChange T) x = x

  act_mul : ∀ {T : Type u} [CommRing T] [Algebra A T] (C C' : WeierstrassCurve.VariableChange T) (x : Raw T),
    act (C * C') x = act C (act C' x)

  curve_act : ∀ {T : Type u} [CommRing T] [Algebra A T] (C : WeierstrassCurve.VariableChange T) (x : Raw T),
    curve (act C x) = C • curve x

  mapRing_act : ∀ {T T' : Type u} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
    (C : WeierstrassCurve.VariableChange T) (x : Raw T),
    mapRing f (act C x) = act (C.map f.toRingHom) (mapRing f x)

namespace RigidWeierstrassData

variable {A : Type u} [CommRing A] (R : RigidWeierstrassData.{u} A)


end RigidWeierstrassData

end ModularCurve
