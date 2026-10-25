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
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section34
open CategoryTheory AlgebraicTopology TopologicalSpace SingularCohomology


noncomputable section

namespace CechCohomology

/-- **Linear equivalence form of the direct-limit isomorphism.**  Packaging
of `cech_cohomology_iso_of_regular_neighborhood_condition` as an honest
`R`-linear equivalence `Module.DirectLimit G f ≃ₗ[R] P` whenever the
`RegularNeighborhoodCondition` holds.  This is the form used downstream
when identifying Čech cohomology of a compact set with the singular
cohomology of a neighborhood. -/
def cechCohomologyLinearEquiv
    {R : Type*} [CommRing R] {ι : Type*} [Preorder ι] [DecidableEq ι]
    {G : ι → Type*} [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
    {f : ∀ i j, i ≤ j → G i →ₗ[R] G j}
    [DirectedSystem G (f · · ·)] [IsDirectedOrder ι] [Nonempty ι]
    {P : Type*} [AddCommGroup P] [Module R P]
    (g : ∀ i, G i →ₗ[R] P)
    (hg : ∀ i j hij x, g j (f i j hij x) = g i x)
    (hreg : RegularNeighborhoodCondition g) :
    Module.DirectLimit G f ≃ₗ[R] P :=
  LinearEquiv.ofBijective
    (Module.DirectLimit.lift R ι G f g hg)
    (cech_cohomology_iso_of_regular_neighborhood_condition g hg hreg)

/-- **Open neighborhoods of a subset `K ⊂ X`.**  The type of pairs
`(U, hKU)` consisting of an open set `U : Opens X` together with a proof
that `K ⊆ U`.  Ordered by *reverse inclusion* (smaller neighborhoods are
"larger" in the poset), this indexes the directed system whose colimit
defines the Čech cohomology of `K`. -/
def OpenNeighborhoods {X : Type*} [TopologicalSpace X] (K : Set X) : Type _ :=
  { U : Opens X // K ⊆ U.1 }

end CechCohomology
end
