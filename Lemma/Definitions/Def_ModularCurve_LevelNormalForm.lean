import Mathlib
import Lemma.Definitions.Def_ModularCurve_KatzLevelP

set_option autoImplicit false

universe u

namespace ModularCurve

def IsNormalForm {T : Type u} [CommRing T] (ℓ : ℕ) (W : WeierstrassCurve T) (D : LevelPData T) : Prop :=
  if ℓ = 3 then
    W.a₂ = 0 ∧ W.a₄ = 0 ∧ W.a₆ = 0 ∧ D.xP = 0 ∧ D.yP = 0 ∧ D.xQ = D.yQ
  else
    W.a₄ = 0 ∧ W.a₆ = 0 ∧ W.a₂ = W.a₃ ∧ D.xP = 0 ∧ D.yP = 0

theorem isNormalForm_of_ne_three {T : Type u} [CommRing T] {ℓ : ℕ} (hℓ : ℓ ≠ 3) (W : WeierstrassCurve T)
    (D : LevelPData T) :
    IsNormalForm ℓ W D ↔ W.a₄ = 0 ∧ W.a₆ = 0 ∧ W.a₂ = W.a₃ ∧ D.xP = 0 ∧ D.yP = 0 := by
  simp [IsNormalForm, hℓ]

theorem isNormalForm_three {T : Type u} [CommRing T] (W : WeierstrassCurve T) (D : LevelPData T) :
    IsNormalForm 3 W D ↔ W.a₂ = 0 ∧ W.a₄ = 0 ∧ W.a₆ = 0 ∧ D.xP = 0 ∧ D.yP = 0 ∧ D.xQ = D.yQ := by
  simp [IsNormalForm]

theorem IsNormalForm.map {T T' : Type u} [CommRing T] [CommRing T'] {ℓ : ℕ} {W : WeierstrassCurve T}
    {D : LevelPData T} (h : IsNormalForm ℓ W D) (f : T →+* T') : IsNormalForm ℓ (W.map f) (D.map f) := by
  unfold IsNormalForm at h ⊢
  split_ifs at h ⊢ with h3
  · obtain ⟨h1, h2, h3', h4, h5, h6⟩ := h
    simp [WeierstrassCurve.map, LevelPData.map, h1, h2, h3', h4, h5, h6]
  · obtain ⟨h1, h2, h3', h4, h5⟩ := h
    simp [WeierstrassCurve.map, LevelPData.map, h1, h2, h3', h4, h5]

end ModularCurve
