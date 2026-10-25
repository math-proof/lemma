/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section38.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.Section17.Part6
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section17
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section26
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section34
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section37
import Def.v1.Atlas.AlgebraicTopologyI.code.Section26.Part8
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section34.Part3
import Instance.v1.Atlas.AlgebraicTopologyI.code.Section37.Part3
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Topology.Category.TopCat.Sphere
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.BallSphere
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.LinearAlgebra.Quotient.Bilinear
import Def.v1.Atlas.AlgebraicTopologyI.code.Section38


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
