/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareExhaustive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquarePrimalConnectivity.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareExhaustive


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC
  StatMech.FrontierD

noncomputable section

theorem fkIsingSquare_fermionicObservable_contour_relation
    (n : Nat) (hn : 0 < n)
    (geometry : FKIsingSquareSwitchingGeometry n hn)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    let D := fkIsingSquareDobrushinDomain n hn
    let edges := fkIsingSquareLocalCarrierDarts n e
    D.fermionicObservable (edges 0) - D.fermionicObservable (edges 1) =
      Complex.I *
        (D.fermionicObservable (edges 2) - D.fermionicObservable (edges 3)) := by
  let D := fkIsingSquareDobrushinDomain n hn
  let L := fkIsingSquare_exhaustiveSwitchingLaw n hn geometry e
  simpa only [D, L, fkIsingSquare_exhaustiveSwitchingLaw] using
    L.fermionicObservable_contour_relation D

end
end StatMech.Universality
