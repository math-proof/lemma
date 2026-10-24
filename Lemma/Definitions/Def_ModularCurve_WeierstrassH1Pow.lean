import Mathlib
import Lemma.Definitions.Def_ModularCurve_WeierstrassGamma1Pow

set_option autoImplicit false

universe u

noncomputable section

open Polynomial

namespace ModularCurve

section Link

variable {T : Type u} [CommRing T]

def inLineMulPoly (W : WeierstrassCurve T) (ℓ n : ℕ) (x₀ : T) : T[X] :=
  ∏ a ∈ Finset.Icc 1 ((ℓ - 1) / 2), (W.Φ n * C ((W.ΨSq a).eval x₀) - C ((W.Φ a).eval x₀) * W.ΨSq n)

theorem inLineMulPoly_map {T' : Type u} [CommRing T'] (f : T →+* T') (W : WeierstrassCurve T) (ℓ n : ℕ) (x₀ : T) :
    inLineMulPoly (W.map f) ℓ n (f x₀) = (inLineMulPoly W ℓ n x₀).map f := by
  simp only [inLineMulPoly, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C,
    WeierstrassCurve.map_Φ, WeierstrassCurve.map_ΨSq, Polynomial.eval_map, Polynomial.eval₂_at_apply]

def IsGamma1Link (W : WeierstrassCurve T) (ℓ M' : ℕ) (h : ↥M'.primeFactors → T[X]) (D : LevelPData T) : Prop :=
  ∀ hmem : ℓ ∈ M'.primeFactors, h ⟨ℓ, hmem⟩ ∣ inLineMulPoly W ℓ (ℓ ^ (M'.factorization ℓ - 1)) D.xP

theorem IsGamma1Link.map {T' : Type u} [CommRing T'] (f : T →+* T') {W : WeierstrassCurve T} {ℓ M' : ℕ}
    {h : ↥M'.primeFactors → T[X]} {D : LevelPData T} (hD : IsGamma1Link W ℓ M' h D) :
    IsGamma1Link (W.map f) ℓ M' (fun p => (h p).map f) (D.map f) :=
  fun hmem => by rw [LevelPData.map_xP, inLineMulPoly_map]; exact Polynomial.map_dvd f (hD hmem)

end Link

namespace LevelComponent

variable {A : Type u} [CommRing A]

def restrict (L : LevelComponent A)
    (P : ∀ {T : Type u} [CommRing T] [Algebra A T], WeierstrassCurve T → L.obj T → Prop)
    (hmap : ∀ {T T' : Type u} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
      (W : WeierstrassCurve T) (x : L.obj T), L.IsLevel W x → P W x → P (W.map f.toRingHom) (L.map f x))
    (hact : ∀ {T : Type u} [CommRing T] [Algebra A T] (C : WeierstrassCurve.VariableChange T)
      (W : WeierstrassCurve T) (x : L.obj T), L.IsLevel W x → P W x → P (C • W) (L.act C x)) :
    LevelComponent A where
  obj := L.obj
  IsLevel W x := L.IsLevel W x ∧ P W x
  map := L.map
  act := L.act
  map_id := L.map_id
  map_comp := L.map_comp
  act_one := L.act_one
  act_mul := L.act_mul
  map_act := L.map_act
  isLevel_map f W x h := ⟨L.isLevel_map f W x h.1, hmap f W x h.1 h.2⟩
  isLevel_act C W x h := ⟨L.isLevel_act C W x h.1, hact C W x h.1 h.2⟩

end LevelComponent

end ModularCurve

namespace WeierstrassCurve.DrinfeldGlobal

def rigidDataH1Pow (A : Type u) [CommRing A] (ℓ M' q : ℕ)
    (hℓ : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsGamma1Point W ℓ D →
        ModularCurve.IsGamma1Point (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (hL : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (d n : ℕ) (h : Polynomial T) (x : T), h ∣ ModularCurve.inLineMulPoly W ℓ n x →
        ModularCurve.kernelVariableChangeDeg C d h ∣
          ModularCurve.inLineMulPoly (C • W) ℓ n (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r)))
    (𝒢 : GroupLaws A) (𝒯 : LevelTransport A 𝒢 q) : ModularCurve.RigidWeierstrassData.{u} A :=
  (((ModularCurve.gamma0PowComponent A M' hM).prod
      ((ModularCurve.gamma1Component A ℓ hℓ).prod (levelComponent A 𝒢 q 𝒯))).restrict
    (fun W x => ModularCurve.IsGamma1Link W ℓ M' x.1 x.2.1)
    (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
    (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem))).toRigid

end WeierstrassCurve.DrinfeldGlobal

end
