/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialIncidence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalBond.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredFullFaces.Part9
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialIncidence.Part5


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open StatMech.FrontierA

noncomputable section

theorem fkIsingSquareInteriorRadialCell_increment_eq_normSq_full_projection
    (n : Nat) (hn : 0 < n)
    (e : FKIsingSquareInteriorRadialCell n) (s : FKIsingMedialSide) :
    fkIsingSquareInteriorRadialIncrement n hn
        (fkIsingSquareInteriorRadialCellIncidence n hn e s) =
      Complex.normSq
        (isingProj (fkIsingSquareWiredDirectedTangent n hn (.dart (e.1, s)))
          (fkIsingSquareWiredFullMedialObservable n hn e.1)) := by
  change fkIsingSquareWiredPrimitiveIncrement n hn (.dart (e.1, s)) = _
  exact fkIsingSquareWiredPrimitiveIncrement_eq_normSq_full_projection
    n hn e.1 s


theorem fkIsingSquareInteriorRadialCell_increment_closed
    (n : Nat) (hn : 0 < n)
    (e : FKIsingSquareInteriorRadialCell n) :
    fkIsingSquareInteriorRadialIncrement n hn
          (fkIsingSquareInteriorRadialCellIncidence n hn e .west) +
        fkIsingSquareInteriorRadialIncrement n hn
          (fkIsingSquareInteriorRadialCellIncidence n hn e .east) =
      fkIsingSquareInteriorRadialIncrement n hn
          (fkIsingSquareInteriorRadialCellIncidence n hn e .south) +
        fkIsingSquareInteriorRadialIncrement n hn
          (fkIsingSquareInteriorRadialCellIncidence n hn e .north) := by
  exact fkIsingSquareWiredPrimitiveIncrement_local_closed n hn e.1

end
end StatMech.Universality
