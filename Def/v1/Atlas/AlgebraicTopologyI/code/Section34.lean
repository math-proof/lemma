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

/-- **Regular-neighborhood condition** (Section 34, Čech-cohomology setup).
For a directed system of `R`-modules `(G i)` with structure maps and a
compatible collection of maps `g i : G i →ₗ[R] P` to a target module `P`,
the system satisfies the regular-neighborhood condition when each index
`i` is dominated by some `j ≥ i` for which `g j` is a *bijection*.  This
abstract criterion captures the geometric situation where, for a compact
subset `K ⊂ X`, the cohomology of every sufficiently small open
neighborhood already agrees with the cohomology of `K`, and is the key
hypothesis allowing the direct-limit (Čech) cohomology to be identified
with a single representative. -/
def RegularNeighborhoodCondition
    {R : Type*} [CommRing R] {ι : Type*} [Preorder ι]
    {G : ι → Type*} [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
    {P : Type*} [AddCommGroup P] [Module R P]
    (g : ∀ i, G i →ₗ[R] P) : Prop :=
  ∀ i, ∃ j, i ≤ j ∧ Function.Bijective (g j)

end CechCohomology
end
