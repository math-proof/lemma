module
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section17.Part6
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section17
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section26
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section34
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section37
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section26.Part8
public import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section34.Part3
public import Instance.v1.Atlas.AlgebraicTopologyI.code.Section37.Part3
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Topology.Category.TopCat.Sphere
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Group.BallSphere
public import Mathlib.Analysis.Normed.Module.RCLike.Basic
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section38.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section38.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

open Metric Set

open Manifold CategoryTheory

namespace PoincareDuality

variable (R : Type) [CommRing R]

/-- The additive commutative group structure on reduced singular homology, inherited
from the augmentation kernel (degree 0) or from singular homology (higher degrees). -/
instance ReducedSingularHomology.instAddCommGroup
    (X : Type) [TopologicalSpace X] (q : ℕ) :
    AddCommGroup (ReducedSingularHomology R X q) := by
  unfold ReducedSingularHomology
  match q with
  | 0 => exact Submodule.addCommGroup _
  | n + 1 => exact (SingularCohomology.singularHomologyModule R (TopCat.of X) (n + 1)).isAddCommGroup

/-- The `R`-module structure on reduced singular homology. -/
instance ReducedSingularHomology.instModule
    (X : Type) [TopologicalSpace X] (q : ℕ) :
    Module R (ReducedSingularHomology R X q) := by
  unfold ReducedSingularHomology
  match q with
  | 0 => exact Submodule.module _
  | n + 1 => exact (SingularCohomology.singularHomologyModule R (TopCat.of X) (n + 1)).isModule

end PoincareDuality
end
