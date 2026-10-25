/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Def.Geometry.Manifold.CollarNeighborhood.Part36
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

theorem collarGluedMap_eq_finite
    {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) (m : ℕ) (z : A × Set.Ico (0 : ℝ) 1)
    (hm : collarPartialWeight g m z.1 = 1) :
    collarGluedMap hA g z = collarFiniteMap hA g m z := by
  exact collarFiniteMap_eq_of_partial_eq_one hA g z
    (collarStageIndex_spec g z.1) hm

theorem collarGluedMap_continuous
    {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) : Continuous (collarGluedMap hA g) := by
  rw [continuous_iff_continuousAt]
  intro z
  obtain ⟨m, hm⟩ := collarPartialWeight_eventually_eq_one g z.1
  have hmevent : ∀ᶠ w in 𝓝 z, collarPartialWeight g m w.1 = 1 :=
    continuousAt_fst.eventually hm
  have heq : collarGluedMap hA g =ᶠ[𝓝 z] collarFiniteMap hA g m := by
    filter_upwards [hmevent] with w hw
    exact collarGluedMap_eq_finite hA g m w hw
  exact (collarFiniteMap_continuous hA g m).continuousAt.congr_of_eventuallyEq heq

theorem collarGluedMap_injective
    {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) : Function.Injective (collarGluedMap hA g) := by
  intro z w hzw
  let m := collarStageIndex g z.1
  let n := collarStageIndex g w.1
  let k := max m n
  have hzm : collarPartialWeight g m z.1 = 1 := collarStageIndex_spec g z.1
  have hwn : collarPartialWeight g n w.1 = 1 := collarStageIndex_spec g w.1
  have hzk : collarPartialWeight g k z.1 = 1 :=
    collarPartialWeight_eq_one_of_le g z.1 hzm (le_max_left _ _)
  have hwk : collarPartialWeight g k w.1 = 1 :=
    collarPartialWeight_eq_one_of_le g w.1 hwn (le_max_right _ _)
  have hfinite : collarFiniteMap hA g k z = collarFiniteMap hA g k w := by
    rw [← collarGluedMap_eq_finite hA g k z hzk,
      ← collarGluedMap_eq_finite hA g k w hwk]
    exact hzw
  apply collarStripMap_isEmbedding.injective
  rw [← collarFiniteMap_recover hA g k z hzk,
    ← collarFiniteMap_recover hA g k w hwk, hfinite]

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
