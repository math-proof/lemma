/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Def.Geometry.Manifold.CollarNeighborhood.Part25
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

theorem collarChartPush_continuous
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (k : ℕ) : Continuous (collarChartPush g k) := by
  apply continuous_fst.prodMk
  apply collarFiberTransform_continuous.comp
  exact ((collarChartPushParameters_continuous g k).comp continuous_fst).prodMk continuous_snd

theorem collarChartPushInv_continuous
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (k : ℕ) : Continuous (collarChartPushInv g k) := by
  apply continuous_fst.prodMk
  apply collarFiberTransform_continuous.comp
  have hp : Continuous (fun z : (g.data k).carrier × Set.Ico (-2 : ℝ) 1 ↦
      collarChartPushParameters g k z.1) :=
    (collarChartPushParameters_continuous g k).comp continuous_fst
  exact ((continuous_snd.comp hp).prodMk (continuous_fst.comp hp)).prodMk continuous_snd

theorem collarChartPush_leftInverse
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (k : ℕ) :
    Function.LeftInverse (collarChartPushInv g k) (collarChartPush g k) := by
  intro z
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    exact collarFiberMap_inverse (collarChartPushParameters g k z.1).1
      (collarChartPushParameters g k z.1).2 z.2

theorem collarChartPush_rightInverse
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (k : ℕ) :
    Function.RightInverse (collarChartPushInv g k) (collarChartPush g k) := by
  intro z
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    exact collarFiberMap_inverse (collarChartPushParameters g k z.1).2
      (collarChartPushParameters g k z.1).1 z.2

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
