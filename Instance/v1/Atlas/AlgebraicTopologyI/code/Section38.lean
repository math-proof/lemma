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
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section38


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

namespace BorsukUlam

attribute [instance] F2CohomRPn.instAddCommGroup

/-- The `ZMod 2`-module structure on `F2CohomRPn n k`, inherited from the underlying
`ModuleCat` object. -/
noncomputable instance F2CohomRPn.instModule (n k : ℕ) : Module (ZMod 2) (F2CohomRPn n k) :=
  ModuleCat.isModule
    (SingularCohomology.singularCohomology (ZMod 2)
      (TopCat.of (RealProjectiveSpace.RPn n))
      (ModuleCat.of (ZMod 2) (ZMod 2)) k)

end BorsukUlam
end
