/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section34.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.Section26.Part8
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section26
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section31
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section33
import Def.v1.Atlas.AlgebraicTopologyI.code.Section31.Part7
import Def.v1.Atlas.AlgebraicTopologyI.code.Section33.Part2
import Mathlib.Algebra.Colimit.Module
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Order.Directed
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Topology.Sets.Opens
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Geometry.Manifold.ChartedSpace
open CategoryTheory AlgebraicTopology TopologicalSpace SingularCohomology


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
