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
public import Instance.v1.Atlas.AlgebraicTopologyI.code.Section38.Part2


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

/-- Convenient abbreviation for the unit sphere `Sⁿ ⊂ ℝⁿ⁺¹` viewed as a subtype. -/
abbrev SphereType (n : ℕ) : Type :=
  ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)

/-- Alexander duality on the sphere: for `K` compact in `Sⁿ` and `1 ≤ q ≤ n - 1`,
the Čech cohomology `Ȟ^q(K; R)` is isomorphic to the reduced singular homology
`\widetilde H_{n-q-1}(Sⁿ \ K; R)`. -/
abbrev singularCohomologyType
    (M : Type) [TopologicalSpace M] (p : ℕ) : Type :=
  (relativeSingularCohomology R M ∅ p : Type)

/-- Convenient `Type` view of singular homology `H_q(M; R)`, defined here as the
relative homology against the empty pair. -/
abbrev singularHomologyType (R : Type) [CommRing R]
    (M : Type) [TopologicalSpace M] (q : ℕ) : Type :=
  (relativeSingularHomology R M ∅ q : Type)

end PoincareDuality
end
