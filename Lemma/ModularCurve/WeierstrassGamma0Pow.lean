import Mathlib
import Lemma.ModularCurve.WeierstrassLevelCarrier
import Def.ModularCurve_WeierstrassLevelModuliDatum
import Def.ModularCurve_WeierstrassLevelComponents
import Lemma.ModularCurve.WeierstrassGamma0Sqf
import Def.WeierstrassCurve_DrinfeldBasisGlobal
import Def.WeierstrassCurve_DrinfeldTransportPin
import Def.WeierstrassCurve_SectionAtOrigin
import Def.WeierstrassCurve_DrinfeldLevelFunctor
import Structure.ModularCurve_WeierstrassGamma0Pow

set_option autoImplicit false

universe u

noncomputable section

open Polynomial

namespace WeierstrassCurve

variable {T : Type u} [CommRing T] (W : WeierstrassCurve T)


theorem IsCyclicGenKernel.monic {p k : ℕ} {h : T[X]} (hh : W.IsCyclicGenKernel p k h) : h.Monic :=
  Polynomial.monic_of_natDegree_le_of_coeff_eq_one _ hh.natDegree_le hh.coeff_eq_one

theorem IsCyclicGenKernel.map {T' : Type u} [CommRing T'] (f : T →+* T') {p k : ℕ} {h : T[X]}
    (hh : W.IsCyclicGenKernel p k h) : (W.map f).IsCyclicGenKernel p k (h.map f) where
  natDegree_le := (Polynomial.natDegree_map_le).trans hh.natDegree_le
  coeff_eq_one := by rw [Polynomial.coeff_map, hh.coeff_eq_one, map_one]
  mul_preΨ_dvd := by
    rw [WeierstrassCurve.map_preΨ, WeierstrassCurve.map_preΨ, ← Polynomial.map_mul]
    exact Polynomial.map_dvd f hh.mul_preΨ_dvd
  dvd_smulNumerator := fun a ha ha' hpa => by
    rw [W.smulNumerator_map f]; exact Polynomial.map_dvd f (hh.dvd_smulNumerator a ha ha' hpa)

end WeierstrassCurve

namespace ModularCurve

variable {T : Type u} [CommRing T]

def gamma0PowDeg (p k : ℕ) : ℕ := if p ^ k = 2 then 1 else Nat.totient (p ^ k) / 2

def IsGamma0PowAt (W : WeierstrassCurve T) (p k : ℕ) (h : T[X]) : Prop :=
  if p ^ k = 2 then W.IsTwoKernel h else W.IsCyclicGenKernel p k h

theorem isGamma0PowAt_of_pow_eq_two (W : WeierstrassCurve T) {p k : ℕ} (hpk : p ^ k = 2) (h : T[X]) :
    IsGamma0PowAt W p k h ↔ W.IsTwoKernel h := by
  simp [IsGamma0PowAt, hpk]

theorem isGamma0PowAt_of_pow_ne_two (W : WeierstrassCurve T) {p k : ℕ} (hpk : p ^ k ≠ 2) (h : T[X]) :
    IsGamma0PowAt W p k h ↔ W.IsCyclicGenKernel p k h := by
  simp [IsGamma0PowAt, hpk]

theorem IsGamma0PowAt.map {T' : Type u} [CommRing T'] (f : T →+* T') (W : WeierstrassCurve T) (p k : ℕ) {h : T[X]}
    (hh : IsGamma0PowAt W p k h) : IsGamma0PowAt (W.map f) p k (h.map f) := by
  by_cases hpk : p ^ k = 2
  · exact (isGamma0PowAt_of_pow_eq_two _ hpk _).2 (((isGamma0PowAt_of_pow_eq_two _ hpk _).1 hh).map W f)
  · exact (isGamma0PowAt_of_pow_ne_two _ hpk _).2 (((isGamma0PowAt_of_pow_ne_two _ hpk _).1 hh).map W f)

def gamma0PowComponent (A : Type u) [CommRing A] (M' : ℕ)
    (hM : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : T[X]), IsGamma0PowAt W p k h →
        IsGamma0PowAt (C • W) p k (kernelVariableChangeDeg C (gamma0PowDeg p k) h)) :
    LevelComponent A where
  obj T _ _ := ↥M'.primeFactors → T[X]
  IsLevel W h := ∀ p : ↥M'.primeFactors, IsGamma0PowAt W (p : ℕ) (M'.factorization (p : ℕ)) (h p)
  map f h := fun p => (h p).map f.toRingHom
  act C h := fun p => kernelVariableChangeDeg C (gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ))) (h p)
  map_id h := funext fun _ => Polynomial.map_id
  map_comp f g h := funext fun p => (Polynomial.map_map f.toRingHom g.toRingHom (h p)).symm
  act_one h := funext fun p => kernelVariableChangeDeg_one _ (h p)
  act_mul C C' h := funext fun p => kernelVariableChangeDeg_mul C C' _ (h p)
  map_act f C h := funext fun p => kernelVariableChangeDeg_map f.toRingHom C _ (h p)
  isLevel_map f W h hh := fun p => IsGamma0PowAt.map f.toRingHom W (p : ℕ) _ (hh p)
  isLevel_act C W h hh := fun p => hM _ W C (p : ℕ) _ (h p) (hh p)

end ModularCurve

namespace WeierstrassCurve.DrinfeldGlobal

def rigidDataPow (A : Type u) [CommRing A] (ℓ M' q : ℕ)
    (hℓ : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (𝒢 : GroupLaws A) (𝒯 : LevelTransport A 𝒢 q) : ModularCurve.RigidWeierstrassData.{u} A :=
  ((ModularCurve.gamma0PowComponent A M' hM).prod
    ((ModularCurve.levelPComponent A ℓ hℓ).prod (levelComponent A 𝒢 q 𝒯))).toRigid

end WeierstrassCurve.DrinfeldGlobal

end
