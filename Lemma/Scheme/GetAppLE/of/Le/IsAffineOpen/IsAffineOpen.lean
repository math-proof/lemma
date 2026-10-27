import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_IsAffineHom_isPushout_map_appLE_appLE_map_of_isAffineOpen](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_IsAffineHom_isPushout_map_appLE_appLE_map_of_isAffineOpen.lean)
-/
@[path]
private lemma main
  {V W : Scheme} {γ : W ⟶ V} [IsAffineHom γ]
  {U U' : V.Opens}
-- given
  (hU : IsAffineOpen U) (hU' : IsAffineOpen U') (h : U ≤ U') :
-- imply
  IsPushout (V.presheaf.map (homOfLE h).op) (γ.appLE U' ((TopologicalSpace.Opens.map γ.base).obj U') le_rfl)
    (γ.appLE U ((TopologicalSpace.Opens.map γ.base).obj U) le_rfl) (W.presheaf.map (homOfLE (γ.preimage_mono h)).op) := by
-- proof
  have H : IsPullback γ (𝟙 W) (𝟙 V) γ := IsPullback.of_vert_isIso ⟨by simp⟩
  have hUST : (TopologicalSpace.Opens.map γ.base).obj U' ≤ (TopologicalSpace.Opens.map γ.base).obj U' := le_rfl
  have hUSX : U ≤ (TopologicalSpace.Opens.map (𝟙 V : V ⟶ V).base).obj U' := h
  have hUY : (TopologicalSpace.Opens.map γ.base).obj U =
      (TopologicalSpace.Opens.map γ.base).obj U ⊓
        (TopologicalSpace.Opens.map (𝟙 W : W ⟶ W).base).obj ((TopologicalSpace.Opens.map γ.base).obj U') :=
    (inf_eq_left.mpr (γ.preimage_mono h)).symm
  have key := (isIso_pushoutSection_iff H hUST hUSX hUY).mp
    (isIso_pushoutSection_of_isAffineOpen H hUST hUSX hUY hU' (hU'.preimage γ) hU)
  have e1 : (𝟙 V : V ⟶ V).appLE U' U hUSX = V.presheaf.map (homOfLE h).op := by
    dsimp only [Scheme.Hom.appLE]
    rw [Scheme.Hom.id_app]
    erw [Category.id_comp]
  have hle : (TopologicalSpace.Opens.map γ.base).obj U ≤ (TopologicalSpace.Opens.map γ.base).obj U' := by
    rw [hUY]
    refine inf_le_right
  have e2 : (𝟙 W : W ⟶ W).appLE ((TopologicalSpace.Opens.map γ.base).obj U')
    ((TopologicalSpace.Opens.map γ.base).obj U) hle =
    W.presheaf.map (homOfLE (γ.preimage_mono h)).op := by
    dsimp only [Scheme.Hom.appLE]
    rw [Scheme.Hom.id_app]
    erw [Category.id_comp]
  rw [e1, e2] at key
  apply key


-- created on 2026-10-20
