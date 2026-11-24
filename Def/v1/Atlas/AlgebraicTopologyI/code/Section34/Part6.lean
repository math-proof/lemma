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
public import Instance.v1.Atlas.AlgebraicTopologyI.code.Section34.Part3
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

/-- **Cohomology of the nerve of an open cover.**  The simplicial complex
(nerve) `N(𝒰)` of an open cover `𝒰` has a vertex for each member of `𝒰`
and a `k`-simplex for each `(k+1)`-tuple with nonempty common
intersection; its singular (= simplicial) cohomology in degree `p` is the
combinatorial input to the Čech-cover construction of `Ȟ^p(Y; R)`. -/
def TopologicalRegularNeighborhoodCondition
    {X : Type*} [TopologicalSpace X] {K : Set X}
    {R : Type*} [CommRing R]
    {H : OpenNeighborhoods K → Type*}
    [∀ U, AddCommGroup (H U)] [∀ U, Module R (H U)]
    {P : Type*} [AddCommGroup P] [Module R P]
    (g : ∀ U : OpenNeighborhoods K, H U →ₗ[R] P) : Prop :=
  ∀ U : OpenNeighborhoods K, ∃ V : OpenNeighborhoods K, U ≤ V ∧ Function.Bijective (g V)

end CechCohomology
end
