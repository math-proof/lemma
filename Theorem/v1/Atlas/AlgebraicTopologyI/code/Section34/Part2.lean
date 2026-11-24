module
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section26.Part8
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section26
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section31
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section33
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section31.Part7
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section33.Part2
public import Mathlib.Algebra.Colimit.Module
public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Order.Directed
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Topology.Sets.Opens
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Abelian.Ext
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section34.Part6
open CategoryTheory AlgebraicTopology TopologicalSpace SingularCohomology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section34.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

namespace CechCohomology

/-- **Čech-cohomology isomorphism in the topological setting.**  For a
closed subset `K` of `X` and a compatible system `g U : H U → P` of maps
from a directed system indexed by open neighborhoods of `K`, the
condition `TopologicalRegularNeighborhoodCondition` implies that the
induced map from the colimit (the Čech cohomology) to `P` is a
bijection.  This is the central technical lemma used to identify
`Ȟ^p(K)` with the cohomology of a regular neighborhood. -/
theorem topological_cech_cohomology_iso
    {X : Type*} [TopologicalSpace X] {K : Set X} (_hK : IsClosed K)
    {R : Type*} [CommRing R] [DecidableEq (OpenNeighborhoods K)]
    {H : OpenNeighborhoods K → Type*}
    [∀ U, AddCommGroup (H U)] [∀ U, Module R (H U)]
    {ρ : ∀ U V : OpenNeighborhoods K, U ≤ V → H U →ₗ[R] H V}
    [DirectedSystem H (ρ · · ·)]
    {P : Type*} [AddCommGroup P] [Module R P]
    (g : ∀ U : OpenNeighborhoods K, H U →ₗ[R] P)
    (hcompat : ∀ U V (h : U ≤ V) x, g V (ρ U V h x) = g U x)
    (hreg : TopologicalRegularNeighborhoodCondition g) :
    Function.Bijective (Module.DirectLimit.lift R (OpenNeighborhoods K) H ρ g hcompat) :=
  cech_cohomology_iso_of_regular_neighborhood_condition g hcompat hreg

end CechCohomology
end
