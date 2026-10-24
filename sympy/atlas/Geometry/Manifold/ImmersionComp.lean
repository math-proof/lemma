/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ImmersionComp.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Geometry.Manifold.Immersion

/-!
# Composition of smooth immersions

This file proves that pointwise and global `C^n` immersions are closed under composition when the
intermediate and target models are boundaryless, for arbitrary differentiability order `n`. No
completeness hypothesis on the model spaces is needed.
-/

open scoped Topology ContDiff
open Manifold

noncomputable section

namespace MathlibExt.Geometry.Manifold.ImmersionCompWanted

universe u

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} {E'' E''' : Type u}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  [NormedAddCommGroup E'''] [NormedSpace 𝕜 E''']
  {H G G' : Type*} [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E'' G}
  {J' : ModelWithCorners 𝕜 E''' G'}
variable {M N N' : Type*}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]
  [TopologicalSpace N'] [ChartedSpace G' N']
variable {n : ℕ∞ω}

private def immersionCompEquiv {F₁ F₂ : Type*}
    [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
    [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
    (e₁ : (E × F₁) ≃L[𝕜] E'') (e₂ : (E'' × F₂) ≃L[𝕜] E''') :
    (E × (F₁ × F₂)) ≃L[𝕜] E''' :=
  (ContinuousLinearEquiv.prodAssoc 𝕜 E F₁ F₂).symm |>.trans
    (e₁.prodCongr (ContinuousLinearEquiv.refl 𝕜 F₂)) |>.trans e₂

private def immersionCompCoordChange [J.Boundaryless]
    (e e' : OpenPartialHomeomorph N G) : OpenPartialHomeomorph E'' E'' :=
  J.toHomeomorph.symm.transOpenPartialHomeomorph <|
    (e.symm.trans e').transHomeomorph J.toHomeomorph

private def immersionCompTargetChange {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [J.Boundaryless]
    (e₂ : (E'' × F) ≃L[𝕜] E''') (e e' : OpenPartialHomeomorph N G) :
    OpenPartialHomeomorph E''' E''' :=
  e₂.toHomeomorph.symm.transOpenPartialHomeomorph <|
    ((immersionCompCoordChange (J := J) e e').symm.prod
      (OpenPartialHomeomorph.refl F)).transHomeomorph e₂.toHomeomorph

private def immersionCompModelTargetChange {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [J.Boundaryless] [J'.Boundaryless]
    (e₂ : (E'' × F) ≃L[𝕜] E''') (e e' : OpenPartialHomeomorph N G) :
    OpenPartialHomeomorph G' G' :=
  J'.toHomeomorph.transOpenPartialHomeomorph <|
    (immersionCompTargetChange (J := J) e₂ e e').transHomeomorph J'.toHomeomorph.symm

private def immersionCompCodChart {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [J.Boundaryless] [J'.Boundaryless]
    (e₂ : (E'' × F) ≃L[𝕜] E''') (e e' : OpenPartialHomeomorph N G)
    (codChart : OpenPartialHomeomorph N' G') : OpenPartialHomeomorph N' G' :=
  codChart.trans (immersionCompModelTargetChange (J := J) (J' := J') e₂ e e')
end MathlibExt.Geometry.Manifold.ImmersionCompWanted
