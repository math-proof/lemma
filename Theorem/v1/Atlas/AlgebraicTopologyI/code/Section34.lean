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
import Def.v1.Atlas.AlgebraicTopologyI.code.Section34
open CategoryTheory AlgebraicTopology TopologicalSpace SingularCohomology


noncomputable section

namespace CechCohomology

/-- **Direct-limit isomorphism under the regular-neighborhood condition**
(Section 34).  If a compatible collection of maps `g i : G i → P` from a
directed system satisfies `RegularNeighborhoodCondition`, then the
canonical map `Module.DirectLimit.lift … g` from the colimit `colim G` to
`P` is *bijective*.  Geometrically, this lets us identify the Čech
cohomology of `K` (the colimit over neighborhoods) with the singular
cohomology of any sufficiently small regular neighborhood.  Surjectivity
follows from one bijective level, injectivity from the cofinality of such
levels. -/
theorem cech_cohomology_iso_of_regular_neighborhood_condition
    {R : Type*} [CommRing R] {ι : Type*} [Preorder ι] [DecidableEq ι]
    {G : ι → Type*} [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
    {f : ∀ i j, i ≤ j → G i →ₗ[R] G j}
    [DirectedSystem G (f · · ·)] [IsDirectedOrder ι] [Nonempty ι]
    {P : Type*} [AddCommGroup P] [Module R P]
    (g : ∀ i, G i →ₗ[R] P)
    (hg : ∀ i j hij x, g j (f i j hij x) = g i x)
    (hreg : RegularNeighborhoodCondition g) :
    Function.Bijective (Module.DirectLimit.lift R ι G f g hg) := by


  constructor
  ·


    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro z hz
    rw [LinearMap.mem_ker] at hz
    obtain ⟨i, x, rfl⟩ := Module.DirectLimit.exists_of z
    simp only [Module.DirectLimit.lift_of] at hz
    obtain ⟨j, hij, hbij⟩ := hreg i
    have h1 : g j (f i j hij x) = 0 := by rw [hg]; exact hz
    have hfx : f i j hij x = 0 := hbij.1 (by rw [h1, map_zero])
    rw [Submodule.mem_bot]
    have : Module.DirectLimit.of R ι G f i x =
        Module.DirectLimit.of R ι G f j (f i j hij x) := by
      rw [Module.DirectLimit.of_f]
    rw [this, hfx, map_zero]
  ·


    intro x
    obtain ⟨i⟩ : Nonempty ι := inferInstance
    obtain ⟨j, _, hbij⟩ := hreg i
    obtain ⟨y, hy⟩ := hbij.2 x
    exact ⟨Module.DirectLimit.of R ι G f j y, by simp [hy]⟩

end CechCohomology
end
