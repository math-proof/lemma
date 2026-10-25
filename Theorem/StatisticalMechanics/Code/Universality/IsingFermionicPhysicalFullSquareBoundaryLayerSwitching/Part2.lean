/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerSwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayer.Part8
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerSwitching


namespace StatMech.Universality

open Finset Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareBoundary_fermionicObservable_contour_relation
    (n : Nat) (hn : 0 < n)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (he : e.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n) :
    let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
    let edges := fkIsingSquareWiredLocalCarrierDarts n e
    D.fermionicObservable (edges 0) - D.fermionicObservable (edges 1) =
      Complex.I *
        (D.fermionicObservable (edges 2) - D.fermionicObservable (edges 3)) := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let L := fkIsingSquareBoundary_exhaustiveSwitchingLaw n hn e he
  simpa only [D, L, fkIsingSquareBoundary_exhaustiveSwitchingLaw] using
    L.fermionicObservable_contour_relation D


end
end StatMech.Universality
