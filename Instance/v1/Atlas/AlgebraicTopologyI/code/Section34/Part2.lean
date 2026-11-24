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
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section34.Part3
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

/-- Inherited abelian-group structure on each level of the Čech family,
forwarded from the `ModuleCat`-valued `nbhdSingCohom`. -/
instance cechFamily_addCommGroup (R : Type) [CommRing R] {X : Type} [TopologicalSpace X]
    (K : Set X) (p : ℕ) (U : OpenNeighborhoods K) :
    AddCommGroup (cechFamily R K p U) :=
  (nbhdSingCohom R U p).isAddCommGroup

/-- Inherited `R`-module structure on each level of the Čech family,
forwarded from the `ModuleCat R`-valued `nbhdSingCohom`. -/
instance cechFamily_module (R : Type) [CommRing R] {X : Type} [TopologicalSpace X]
    (K : Set X) (p : ℕ) (U : OpenNeighborhoods K) :
    Module R (cechFamily R K p U) :=
  (nbhdSingCohom R U p).isModule

end CechCohomology
end
