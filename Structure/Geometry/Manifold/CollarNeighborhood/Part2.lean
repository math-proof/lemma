/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Theorem.Geometry.Manifold.CollarNeighborhood.Part22
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

structure collarGluingCover
    (X : Type*) [TopologicalSpace X] (A : Set X) where
  data : ℕ → collarLocalData X A
  compact_closure : ∀ k, IsCompact (closure (data k).carrier)
  cover : (Set.univ : Set A) ⊆ ⋃ k, (data k).carrier
  weight : PartitionOfUnity ℕ A Set.univ
  subordinate : weight.IsSubordinate fun k ↦ (data k).carrier

structure collarControlledCover
    (X : Type*) [TopologicalSpace X] (A : Set X) where
  data : ℕ → collarLocalData X A
  compact_closure : ∀ k, IsCompact (closure (data k).carrier)
  cover : (Set.univ : Set A) ⊆ ⋃ k, (data k).carrier
  ambient : ℕ → Set X
  ambient_open : ∀ k, IsOpen (ambient k)
  ambient_locallyFinite : LocallyFinite ambient
  carrier_to_ambient : ∀ k (a : A), a ∈ (data k).carrier → a.val ∈ ambient k
  weight : PartitionOfUnity ℕ A Set.univ
  subordinate : weight.IsSubordinate fun k ↦ (data k).carrier

structure collarPreparedCover
    (X : Type*) [TopologicalSpace X] (A : Set X) where
  data : ℕ → collarLocalData X A
  ambient : ℕ → Set X
  ambient_open : ∀ k, IsOpen (ambient k)
  ambient_locallyFinite : LocallyFinite ambient
  carrier_to_ambient : ∀ k (a : A), a ∈ (data k).carrier → a.val ∈ ambient k
  weight : PartitionOfUnity ℕ A Set.univ
  subordinate : weight.IsSubordinate fun k ↦ (data k).carrier
  compact_tsupport : ∀ k, IsCompact (tsupport (weight k))
  tube : ∀ k (a : (data k).carrier), a.val ∈ tsupport (weight k) →
    ∀ t : Set.Ico (0 : ℝ) 1, (data k).map (a, t) ∈ ambient k

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
