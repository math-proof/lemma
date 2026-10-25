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


noncomputable section

open Metric Set

namespace BorsukUlam

/-- The `k`-th singular cohomology of real projective `n`-space `ℝPⁿ` with coefficients in
`𝔽₂ = ZMod 2`, packaged as a plain `Type`. Used to set up the Borsuk–Ulam proof via the
mod-2 cohomology ring of `ℝPⁿ`. -/
def F2CohomRPn (n k : ℕ) : Type :=
  (SingularCohomology.singularCohomology (ZMod 2)
    (TopCat.of (RealProjectiveSpace.RPn n))
    (ModuleCat.of (ZMod 2) (ZMod 2)) k : Type)

/-- The additive commutative group structure on `F2CohomRPn n k` inherited from its
`ModuleCat` representation. -/
@[reducible] def F2CohomRPn.instAddCommGroup (n k : ℕ) : AddCommGroup (F2CohomRPn n k) :=
  ModuleCat.isAddCommGroup
    (SingularCohomology.singularCohomology (ZMod 2)
      (TopCat.of (RealProjectiveSpace.RPn n))
      (ModuleCat.of (ZMod 2) (ZMod 2)) k)

attribute [instance] F2CohomRPn.instAddCommGroup

/-- The cup product `H^p(ℝPⁿ; 𝔽₂) ⊗ H^q(ℝPⁿ; 𝔽₂) → H^{p+q}(ℝPⁿ; 𝔽₂)` on mod-2 cohomology
of `ℝPⁿ`, exposed as a binary function on the underlying types. -/
noncomputable def F2CohomRPn.cupProduct (n p q : ℕ) :
    F2CohomRPn n p → F2CohomRPn n q → F2CohomRPn n (p + q) :=
  fun a b => (SingularCohomology.cupProduct (ZMod 2)
    (TopCat.of (RealProjectiveSpace.RPn n)) p q) (a ⊗ₜ[ZMod 2] b)

end BorsukUlam
end
