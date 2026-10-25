/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Theorem.Geometry.Manifold.CollarNeighborhood.Part29
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

def collarExtendByIdentity
    {Y : Type*} [TopologicalSpace Y] (R C : Set Y) (e : R ≃ₜ R)
    (hR : IsOpen R) (hC : IsClosed C) (hCR : C ⊆ R)
    (he : ∀ x : R, x.val ∉ C → e x = x)
    (he' : ∀ x : R, x.val ∉ C → e.symm x = x) : Y ≃ₜ Y where
  toFun := collarExtendByIdentityFun R e
  invFun := collarExtendByIdentityInv R e
  left_inv := collarExtendByIdentity_leftInverse R e
  right_inv := collarExtendByIdentity_rightInverse R e
  continuous_toFun := collarExtendByIdentity_continuous R C e hR hC hCR he
  continuous_invFun := collarExtendByIdentity_continuous R C e.symm hR hC hCR he'

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
