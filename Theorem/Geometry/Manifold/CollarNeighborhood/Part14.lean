/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Def.Geometry.Manifold.CollarNeighborhood.Part13
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

theorem collarExtendedChart_val_of_nonpos
    {X : Type*} [TopologicalSpace X] {A : Set X} (d : collarLocalData X A)
    (z : d.carrier × Set.Ico (-2 : ℝ) 1) (hz : z.2.val ≤ 0) :
    (collarExtendedChart d z).val = (z.1.val.val, z.2.val) := by
  simp [collarExtendedChart, hz]

theorem collarExtendedChart_val_of_pos
    {X : Type*} [TopologicalSpace X] {A : Set X} (d : collarLocalData X A)
    (z : d.carrier × Set.Ico (-2 : ℝ) 1) (hz : 0 < z.2.val) :
    (collarExtendedChart d z).val =
      (d.map (z.1, ⟨z.2.val, hz.le, z.2.property.2⟩), 0) := by
  rw [collarExtendedChart, dite_eq_right (not_le_of_gt hz)]
  rfl

theorem collarExtendedChart_val_of_nonneg
    {X : Type*} [TopologicalSpace X] {A : Set X} (d : collarLocalData X A)
    (z : d.carrier × Set.Ico (-2 : ℝ) 1) (hz : 0 ≤ z.2.val) :
    (collarExtendedChart d z).val =
      (d.map (z.1, ⟨z.2.val, hz, z.2.property.2⟩), 0) := by
  rcases hz.eq_or_lt with hz0 | hzpos
  · have hz0' : z.2.val = 0 := hz0.symm
    rw [collarExtendedChart_val_of_nonpos d z hz0'.le]
    have hcoord : (⟨z.2.val, hz, z.2.property.2⟩ : Set.Ico (0 : ℝ) 1) =
        ⟨0, by simp⟩ := by
      apply Subtype.ext
      exact hz0'
    rw [hcoord, d.map_zero z.1, hz0']
  · exact collarExtendedChart_val_of_pos d z hzpos

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
