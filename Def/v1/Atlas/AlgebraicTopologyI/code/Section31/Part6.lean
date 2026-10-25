/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section31.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.Section26.Part8
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section26
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section32
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Lemma32_4
import Def.v1.Atlas.AlgebraicTopologyI.code.Section32.Part2
import Def.v1.Atlas.AlgebraicTopologyI.code.Lemma32_4
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.CategoryTheory.Action.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.RepresentationTheory.Rep.Iso
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.LocallyConstant.Basic
import Abbrev.v1.Atlas.AlgebraicTopologyI.code.Section31.Part2
open Topology MulAction CategoryTheory TopologicalSpace

open CategoryTheory AlgebraicTopology SingularCohomology Limits


noncomputable section

namespace OrientationHomology

/-- Absolute singular homology agrees with relative homology against the empty subspace,
`H_n(M; R) ≅ H_n(M, ∅; R)`. -/
def singularHomology_iso_relativeHomology_empty (R : Type) [CommRing R]
    (n : ℕ) (M : Type) [TopologicalSpace M] :
    singularHomologyModule R (TopCat.of M) n ≅ relativeHomologyModule R n M ∅ := by


  show ((singularChainFunctor R).obj (TopCat.of M)).homology n ≅
    (cokernel ((singularChainFunctor R).map (subsetIncl M ∅))).homology n

  have hf : (singularChainFunctor R).map (subsetIncl M ∅) = 0 := by
    haveI : IsEmpty (↥(∅ : Set M)) := Set.isEmpty_coe_sort.mpr rfl
    haveI : TotallyDisconnectedSpace (↥(∅ : Set M)) := inferInstance
    have hZ : IsZero ((singularChainFunctor R).obj (TopCat.of (↥(∅ : Set M)))) := by
      apply IsZero.of_iso _ (singularChainComplexFunctorIsoOfTotallyDisconnectedSpace
        (ModuleCat.{0} R) (ModuleCat.of R R) (TopCat.of (↥(∅ : Set M))))
      have hCoprod : IsZero (∐ fun _ : (↥(∅ : Set M)) ↦ (ModuleCat.of R R)) := by
        rw [IsZero.iff_id_eq_zero]; ext ⟨j, hj⟩; exact absurd hj (by simp)
      rw [IsZero.iff_id_eq_zero]; ext i : 1
      simp only [HomologicalComplex.id_f, HomologicalComplex.zero_f_apply]
      exact hCoprod.eq_zero_of_src (𝟙 _) ▸ rfl
    exact hZ.eq_zero_of_src _

  have iso_chain : cokernel ((singularChainFunctor R).map (subsetIncl M ∅)) ≅
      (singularChainFunctor R).obj (TopCat.of M) := by
    rw [hf]
    exact cokernelZeroIsoTarget
  exact ((HomologicalComplex.homologyFunctor _ _ n).mapIso iso_chain).symm

end OrientationHomology
end
