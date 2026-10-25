/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointClampedTarget.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCompactPlacement.Part4
import Def.StatisticalMechanics.Code.Universality.IsingFermionicEndpointClampedTarget


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem isingFiniteGraphLaplacian_boundaryClamp_sub_le_four
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (boundary : V -> Prop) (value : Real) (f : V -> Real) (x : V)
    (hx : Not (boundary x)) (traceBound : Real)
    (htrace_nonneg : 0 <= traceBound)
    (hcard : Nat.card (G.neighborSet x) <= 4)
    (htrace : forall y, boundary y -> |value - f y| <= traceBound) :
    |isingFiniteGraphLaplacian G
          (isingBoundaryClamp boundary value f) x -
        isingFiniteGraphLaplacian G f x| <= 4 * traceBound := by
  classical
  have hcardFinset : (G.neighborFinset x).card <= 4 := by
    have hncard : Nat.card (G.neighborSet x) = G.degree x :=
      (Nat.card_eq_fintype_card).trans
        (SimpleGraph.card_neighborSet_eq_degree G x)
    rw [SimpleGraph.card_neighborFinset_eq_degree, <- hncard]
    exact hcard
  unfold isingFiniteGraphLaplacian
  rw [<- Finset.sum_sub_distrib]
  calc
    |∑ y ∈ G.neighborFinset x,
        ((isingBoundaryClamp boundary value f y -
            isingBoundaryClamp boundary value f x) - (f y - f x))| <=
        ∑ y ∈ G.neighborFinset x,
          |(isingBoundaryClamp boundary value f y -
            isingBoundaryClamp boundary value f x) - (f y - f x)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ _y ∈ G.neighborFinset x, traceBound := by
      apply Finset.sum_le_sum
      intro y _hy
      by_cases hy : boundary y
      · simpa [isingBoundaryClamp, hx, hy] using htrace y hy
      · simpa [isingBoundaryClamp, hx, hy] using htrace_nonneg
    _ = ((G.neighborFinset x).card : Real) * traceBound := by simp
    _ <= 4 * traceBound := by
      gcongr
      exact_mod_cast hcardFinset


theorem isingFiniteGhostLaplacian_boundaryClamp_sub_le_four
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (ghostRate : V -> Real) (boundary : V -> Prop)
    (value ghostValue : Real) (f : V -> Real) (x : V)
    (hx : Not (boundary x)) (traceBound : Real)
    (htrace_nonneg : 0 <= traceBound)
    (hcard : Nat.card (G.neighborSet x) <= 4)
    (htrace : forall y, boundary y -> |value - f y| <= traceBound) :
    |isingFiniteWeightedLaplacian
          (isingFiniteGhostConductance G ghostRate)
          (isingFiniteGhostExtension ghostValue
            (isingBoundaryClamp boundary value f)) (some x) -
        isingFiniteWeightedLaplacian
          (isingFiniteGhostConductance G ghostRate)
          (isingFiniteGhostExtension ghostValue f) (some x)| <=
      4 * traceBound := by
  rw [isingFiniteGhostLaplacian_some, isingFiniteGhostLaplacian_some]
  have hgraph := isingFiniteGraphLaplacian_boundaryClamp_sub_le_four
    G boundary value f x hx traceBound htrace_nonneg hcard htrace
  simpa [isingBoundaryClamp, hx] using hgraph


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
