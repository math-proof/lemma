/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section34.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.AlgebraicTopologyI.code.Section26.Part8
public import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section26
public import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section31
public import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section33
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
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section34.Part4
open CategoryTheory AlgebraicTopology TopologicalSpace SingularCohomology


public noncomputable section

namespace CechCohomology

/-- **An open cover of a topological space `Y`.**  Data of a collection of
open subsets `members ⊂ Opens Y` whose union is all of `Y`.  The set of
open covers, ordered by *refinement*, indexes the directed system used in
the Čech-cover (nerve) construction of Čech cohomology — an alternative,
combinatorial description that agrees with the neighborhood definition
for sufficiently nice spaces. -/
structure OpenCover (Y : Type) [TopologicalSpace Y] where
  members : Set (Opens Y)
  covers : ∀ y : Y, ∃ U ∈ members, y ∈ (U : Set Y)

end CechCohomology
end
