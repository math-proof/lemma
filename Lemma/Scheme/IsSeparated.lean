import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma mapDesc_openCover_proof
  {N S : Scheme} (g : N ⟶ S) (𝒰 : Scheme.OpenCover N)
  (h : ∀ i j : 𝒰.I₀, IsClosedImmersion (pullback.mapDesc (𝒰.f i) (𝒰.f j) g)) :
  IsSeparated g := by
  constructor
  refine IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion)
    (Scheme.Pullback.openCoverOfLeftRight 𝒰 𝒰 g g) fun ij => ?_
  obtain ⟨i, j⟩ := ij
  have hsq := pullback_map_diagonal_isPullback (𝒰.f i) (𝒰.f j) g
  change IsClosedImmersion (pullback.snd (pullback.diagonal g)
    (pullback.map (𝒰.f i ≫ g) (𝒰.f j ≫ g) g g (𝒰.f i) (𝒰.f j) (𝟙 _) (Category.comp_id _) (Category.comp_id _)))
  have key : hsq.isoPullback.inv ≫ pullback.mapDesc (𝒰.f i) (𝒰.f j) g = pullback.snd (pullback.diagonal g)
    (pullback.map (𝒰.f i ≫ g) (𝒰.f j ≫ g) g g (𝒰.f i) (𝒰.f j) (𝟙 _) (Category.comp_id _) (Category.comp_id _)) := by
    rw [Iso.inv_comp_eq]
    apply hsq.isoPullback_hom_snd.symm
  rw [← key]
  let _ := h i j
  infer_instance
/--
[AlgebraicGeometry_IsSeparated_of_isClosedImmersion_mapDesc_openCover](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_IsSeparated_of_isClosedImmersion_mapDesc_openCover.lean)
-/
@[path]
private lemma main
  {N S : Scheme} (g : N ⟶ S) (𝒰 : Scheme.OpenCover N)
  (h : ∀ i j : 𝒰.I₀, IsClosedImmersion (pullback.mapDesc (𝒰.f i) (𝒰.f j) g)) :
-- imply
  IsSeparated g := by
-- proof
  apply mapDesc_openCover_proof g 𝒰 h


-- created on 2026-10-20
