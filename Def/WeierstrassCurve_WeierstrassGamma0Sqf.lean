module
public import Mathlib
public import Theorem.Polynomial.WeierstrassLevelCarrier
public import Def.ModularCurve_WeierstrassLevelModuliDatum
public import Def.ModularCurve_WeierstrassLevelComponents
public import Def.WeierstrassCurve_DrinfeldBasisGlobal
public import Def.WeierstrassCurve_DrinfeldTransportPin
public import Def.WeierstrassCurve_SectionAtOrigin
public import Def.WeierstrassCurve_DrinfeldLevelFunctor
public import Structure.ModularCurve_WeierstrassGamma0Sqf
set_option autoImplicit false


public section

universe u

noncomputable section

open Polynomial


namespace ModularCurve

variable {T : Type u} [CommRing T]

def gamma0Deg (p : ℕ) : ℕ := if p = 2 then 1 else (p - 1) / 2

def IsGamma0At (W : WeierstrassCurve T) (p : ℕ) (h : T[X]) : Prop :=
  if p = 2 then W.IsTwoKernel h else W.IsCyclicKernel p h

def gamma0SqfComponent (A : Type u) [CommRing A] (M' : ℕ)
    (hM : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p : ℕ) (h : T[X]), IsGamma0At W p h → IsGamma0At (C • W) p (kernelVariableChangeDeg C (gamma0Deg p) h)) :
    LevelComponent A where
  obj T _ _ := ↥M'.primeFactors → T[X]
  IsLevel W h := ∀ p : ↥M'.primeFactors, IsGamma0At W (p : ℕ) (h p)
  map f h := fun p => (h p).map f.toRingHom
  act C h := fun p => kernelVariableChangeDeg C (gamma0Deg (p : ℕ)) (h p)
  map_id h := funext fun _ => Polynomial.map_id
  map_comp f g h := funext fun p => (Polynomial.map_map f.toRingHom g.toRingHom (h p)).symm
  act_one h := funext fun p => kernelVariableChangeDeg_one _ (h p)
  act_mul C C' h := funext fun p => kernelVariableChangeDeg_mul C C' _ (h p)
  map_act f C h := funext fun p => kernelVariableChangeDeg_map f.toRingHom C _ (h p)
  isLevel_map f W h hh := fun p => IsGamma0At.map f.toRingHom W (p : ℕ) (hh p)
  isLevel_act C W h hh := fun p => hM _ W C (p : ℕ) (h p) (hh p)

end ModularCurve

namespace WeierstrassCurve.DrinfeldGlobal

def rigidDataSqf (A : Type u) [CommRing A] (ℓ M' q : ℕ)
    (hℓ : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p : ℕ) (h : Polynomial T), ModularCurve.IsGamma0At W p h →
        ModularCurve.IsGamma0At (C • W) p (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0Deg p) h))
    (𝒢 : GroupLaws A) (𝒯 : LevelTransport A 𝒢 q) : ModularCurve.RigidWeierstrassData.{u} A :=
  ((ModularCurve.gamma0SqfComponent A M' hM).prod
    ((ModularCurve.levelPComponent A ℓ hℓ).prod (levelComponent A 𝒢 q 𝒯))).toRigid

end WeierstrassCurve.DrinfeldGlobal

end
