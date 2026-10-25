/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryCancellation.Part7
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayer.Part8


namespace StatMech.Universality

open Finset Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

@[simp] theorem fkIsingSquareBoundaryLayerRadialIncrement_mk
    (n : Nat) (hn : 0 < n) (d : FKIsingSquareInteriorRadialDart n) :
    fkIsingSquareBoundaryLayerRadialIncrement n hn (Quot.mk _ d) =
      Complex.normSq
        ((fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart d.1)) := rfl

theorem fkIsingSquareBoundaryLayerRadialIncrement_nonneg
    (n : Nat) (hn : 0 < n)
    (e : FKIsingSquareInteriorRadialIncidence n hn) :
    0 <= fkIsingSquareBoundaryLayerRadialIncrement n hn e := by
  induction e using Quot.ind with
  | _ d => exact Complex.normSq_nonneg _

end
end StatMech.Universality
