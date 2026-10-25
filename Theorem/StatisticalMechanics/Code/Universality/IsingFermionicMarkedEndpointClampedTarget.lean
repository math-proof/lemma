/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMarkedEndpointClampedTarget.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryProjectedPrimitiveConvergence


namespace StatMech.Universality

open Filter

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem isingFiniteGraphLaplacian_eq_of_eq_on_neighbors
    {V : Type*} [Fintype V] (G : SimpleGraph V) (f g : V -> Real) (x : V)
    (hx : f x = g x) (hneighbor : forall y, G.Adj x y -> f y = g y) :
    isingFiniteGraphLaplacian G f x = isingFiniteGraphLaplacian G g x := by
  classical
  unfold isingFiniteGraphLaplacian
  apply Finset.sum_congr rfl
  intro y hy
  rw [hx, hneighbor y ((mem_neighborFinset G x y).mp hy)]

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
