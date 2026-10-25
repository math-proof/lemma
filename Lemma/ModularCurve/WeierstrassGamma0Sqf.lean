import Mathlib
import Lemma.ModularCurve.WeierstrassLevelCarrier
import Def.ModularCurve_WeierstrassLevelModuliDatum
import Def.ModularCurve_WeierstrassLevelComponents
import Def.WeierstrassCurve_DrinfeldBasisGlobal
import Def.WeierstrassCurve_DrinfeldTransportPin
import Def.WeierstrassCurve_SectionAtOrigin
import Def.WeierstrassCurve_DrinfeldLevelFunctor
import Structure.ModularCurve_WeierstrassGamma0Sqf

set_option autoImplicit false

universe u

noncomputable section

open Polynomial

namespace WeierstrassCurve

variable {T : Type u} [CommRing T] (W : WeierstrassCurve T)


theorem IsTwoKernel.monic {h : T[X]} (hh : W.IsTwoKernel h) : h.Monic :=
  Polynomial.monic_of_natDegree_le_of_coeff_eq_one _ hh.natDegree_le hh.coeff_eq_one

theorem IsTwoKernel.map {T' : Type u} [CommRing T'] (f : T →+* T') {h : T[X]} (hh : W.IsTwoKernel h) :
    (W.map f).IsTwoKernel (h.map f) where
  natDegree_le := (Polynomial.natDegree_map_le).trans hh.natDegree_le
  coeff_eq_one := by rw [Polynomial.coeff_map, hh.coeff_eq_one, map_one]
  dvd_Ψ₂Sq := by rw [WeierstrassCurve.map_Ψ₂Sq]; exact Polynomial.map_dvd f hh.dvd_Ψ₂Sq

end WeierstrassCurve

namespace ModularCurve

variable {T : Type u} [CommRing T]

def gamma0Deg (p : ℕ) : ℕ := if p = 2 then 1 else (p - 1) / 2

def IsGamma0At (W : WeierstrassCurve T) (p : ℕ) (h : T[X]) : Prop :=
  if p = 2 then W.IsTwoKernel h else W.IsCyclicKernel p h

theorem isGamma0At_two (W : WeierstrassCurve T) (h : T[X]) : IsGamma0At W 2 h ↔ W.IsTwoKernel h := by
  simp [IsGamma0At]

theorem isGamma0At_of_ne_two (W : WeierstrassCurve T) {p : ℕ} (hp : p ≠ 2) (h : T[X]) :
    IsGamma0At W p h ↔ W.IsCyclicKernel p h := by
  simp [IsGamma0At, hp]

theorem IsGamma0At.map {T' : Type u} [CommRing T'] (f : T →+* T') (W : WeierstrassCurve T) (p : ℕ) {h : T[X]}
    (hh : IsGamma0At W p h) : IsGamma0At (W.map f) p (h.map f) := by
  by_cases hp : p = 2
  · subst hp
    exact (isGamma0At_two _ _).2 (((isGamma0At_two _ _).1 hh).map W f)
  · exact (isGamma0At_of_ne_two _ hp _).2 (((isGamma0At_of_ne_two _ hp _).1 hh).map W f)

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
