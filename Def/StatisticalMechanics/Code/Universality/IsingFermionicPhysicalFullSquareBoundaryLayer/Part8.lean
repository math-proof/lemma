/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryCancellation.Part7
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayer.Part7


namespace StatMech.Universality

open Finset Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

noncomputable def fkIsingSquareBoundaryLayerRadialIncrement
    (n : Nat) (hn : 0 < n) :
    FKIsingSquareInteriorRadialIncidence n hn -> Real :=
  Quot.lift (fun d : FKIsingSquareInteriorRadialDart n =>
      Complex.normSq
        ((fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart d.1)))
    (fun _ _ hxy => fkIsingSquareBoundaryLayer_eq_of_sameCycle_of_step
      (fkIsingSquareInteriorRadialBondPerm n hn)
      (fun d : FKIsingSquareInteriorRadialDart n =>
        Complex.normSq
          ((fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
            (.dart d.1)))
      (fun d => by
        change Complex.normSq
            ((fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
              (.dart (fkIsingSquareInteriorRadialBondMate n hn d).1)) =
          Complex.normSq
            ((fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
              (.dart d.1))
        rw [<- fkIsingSquareBoundaryLayer_fermionicObservable_incidence
          n hn (fkIsingSquareInteriorRadialBondMate n hn d).1]
        change Complex.normSq
            ((fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
              (.bond (fkIsingSquareWiredBondMate n hn d.1))) = _
        rw [fkIsingSquareBoundaryLayer_fermionicObservable_bondMate
            n hn d.1
              (fkIsingSquareInteriorRadialDart_ne_source n hn d)
              (fkIsingSquareInteriorRadialDart_ne_terminal n hn d),
          Complex.normSq_mul, fkIsingSquareWiredBondPhase_normSq, mul_one,
          fkIsingSquareBoundaryLayer_fermionicObservable_incidence])
      hxy)

end
end StatMech.Universality
