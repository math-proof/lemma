import Mathlib
import Lemma.Definitions.Def_ModularCurve_WeierstrassGamma0Pow

set_option autoImplicit false

universe u

namespace ModularCurve

structure IsGamma1Point {A : Type u} [CommRing A] (W : WeierstrassCurve A) (ℓ : ℕ) (D : LevelPData A) : Prop where

  equation_P : W.toAffine.Equation D.xP D.yP

  preΨ_P : (W.preΨ ℓ).eval D.xP = 0

  xQ_eq : D.xQ = D.xP

  yQ_eq : D.yQ = D.yP

namespace IsGamma1Point

variable {A : Type u} {B : Type u} [CommRing A] [CommRing B] {W : WeierstrassCurve A} {ℓ : ℕ} {D : LevelPData A}

theorem map (h : IsGamma1Point W ℓ D) (f : A →+* B) : IsGamma1Point (W.map f) ℓ (D.map f) where
  equation_P := h.equation_P.map f
  preΨ_P := by
    rw [LevelPData.map_xP, WeierstrassCurve.map_preΨ, Polynomial.eval_map, Polynomial.eval₂_at_apply, h.preΨ_P, map_zero]
  xQ_eq := by rw [LevelPData.map_xQ, LevelPData.map_xP, h.xQ_eq]
  yQ_eq := by rw [LevelPData.map_yQ, LevelPData.map_yP, h.yQ_eq]

end IsGamma1Point

noncomputable def gamma1Component (A : Type u) [CommRing A] (ℓ : ℕ)
    (hℓ : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : LevelPData T), IsGamma1Point W ℓ D → IsGamma1Point (C • W) ℓ (D.variableChange C)) :
    LevelComponent A where
  obj T _ _ := LevelPData T
  IsLevel W D := IsGamma1Point W ℓ D
  map f D := D.map f.toRingHom
  act C D := D.variableChange C
  map_id _ := rfl
  map_comp _ _ _ := rfl
  act_one D := LevelPData.variableChange_one D
  act_mul C C' D := LevelPData.variableChange_mul C C' D
  map_act f C D := LevelPData.map_variableChange f.toRingHom C D
  isLevel_map f _ _ hD := hD.map f.toRingHom
  isLevel_act C W D hD := hℓ _ W C D hD

end ModularCurve

namespace WeierstrassCurve.DrinfeldGlobal

noncomputable def rigidDataGamma1Pow (A : Type u) [CommRing A] (ℓ M' q : ℕ)
    (hℓ : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsGamma1Point W ℓ D →
        ModularCurve.IsGamma1Point (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (𝒢 : GroupLaws A) (𝒯 : LevelTransport A 𝒢 q) : ModularCurve.RigidWeierstrassData.{u} A :=
  ((ModularCurve.gamma0PowComponent A M' hM).prod
    ((ModularCurve.gamma1Component A ℓ hℓ).prod (levelComponent A 𝒢 q 𝒯))).toRigid

end WeierstrassCurve.DrinfeldGlobal
