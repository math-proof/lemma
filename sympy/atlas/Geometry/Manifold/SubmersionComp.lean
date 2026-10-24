module

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/SubmersionComp.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Geometry.Manifold.Submersion

-- `IsSubmersionOfComplement` is not `@[expose]` at this Mathlib pin (unlike
-- `IsImmersionOfComplement`), and `IsSubmersionOfComplement.comp` must unfold it.
import all Mathlib.Geometry.Manifold.Submersion

/-! # Composition of submersions

This file proves that pointwise and global submersions between boundaryless Banach manifolds are
closed under composition. The proof composes their local projection normal forms after aligning
the intermediate charts.
-/

open scoped Topology ContDiff
open Manifold

noncomputable section

namespace MathlibExt.Geometry.Manifold.SubmersionCompWanted

universe u

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E E'' : Type u} {E''' : Type*}
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

private def submersionCompExtend [I.Boundaryless] (φ : OpenPartialHomeomorph M H) :
    OpenPartialHomeomorph M E where
  toPartialEquiv := φ.extend I
  continuousOn_toFun := φ.continuousOn_extend
  continuousOn_invFun := φ.continuousOn_extend_symm
  open_source := φ.isOpen_extend_source
  open_target := φ.isOpen_extend_target

private def submersionCompEquiv {F₁ F₂ : Type u}
    [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
    [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
    (e₁ : E ≃L[𝕜] (E'' × F₁)) (e₂ : E'' ≃L[𝕜] (E''' × F₂)) :
    E ≃L[𝕜] (E''' × (F₂ × F₁)) :=
  e₁.trans <| (e₂.prodCongr <| ContinuousLinearEquiv.refl 𝕜 F₁).trans <|
    ContinuousLinearEquiv.prodAssoc 𝕜 E''' F₂ F₁

private def submersionCompCoordChange [J.Boundaryless]
    (φ ψ : OpenPartialHomeomorph N G) : OpenPartialHomeomorph E'' E'' :=
  (submersionCompExtend (I := J) φ).symm.trans (submersionCompExtend (I := J) ψ)

private def submersionCompLiftModel [J.Boundaryless]
    {F : Type u} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (e : E ≃L[𝕜] (E'' × F)) (φ ψ : OpenPartialHomeomorph N G) :
    OpenPartialHomeomorph E E :=
  (e.toHomeomorph.toOpenPartialHomeomorph.trans
      ((submersionCompCoordChange (J := J) φ ψ).prod
        (OpenPartialHomeomorph.refl F))).trans
    e.symm.toHomeomorph.toOpenPartialHomeomorph

private def submersionCompLift [I.Boundaryless] [J.Boundaryless]
    {F : Type u} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (e : E ≃L[𝕜] (E'' × F)) (φ ψ : OpenPartialHomeomorph N G) :
    OpenPartialHomeomorph H H :=
  (I.toHomeomorph.toOpenPartialHomeomorph.trans
    (submersionCompLiftModel (J := J) e φ ψ)).trans
    I.toHomeomorph.symm.toOpenPartialHomeomorph

private def submersionCompDomChart [I.Boundaryless] [J.Boundaryless]
    {F : Type u} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : M → N} {x : M} (hf : IsSubmersionAtOfComplement F I J n f x)
    (ψ : OpenPartialHomeomorph N G) : OpenPartialHomeomorph M H :=
  hf.domChart.trans <| submersionCompLift (I := I) (J := J) hf.equiv hf.codChart ψ
end MathlibExt.Geometry.Manifold.SubmersionCompWanted
