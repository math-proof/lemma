/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialRectangle.Part6
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalDirichletLimit.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialPatch.Part5


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open Filter Set Topology

noncomputable section

theorem fkIsingSquareRadialPatchIncidence_increment_eq_normSq_full_projection
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n)
    (i j : Fin m) (s : FKIsingMedialSide) :
    fkIsingSquareInteriorRadialIncrement n hn
        (fkIsingSquareRadialPatchIncidence n m hn hm i j s) =
      Complex.normSq
        (isingProj
          (fkIsingSquareWiredDirectedTangent n hn
            (.dart (fkIsingSquareRadialPatchEdge n m hm i j, s)))
          (fkIsingSquareWiredFullMedialObservable n hn
            (fkIsingSquareRadialPatchEdge n m hm i j))) := by
  exact fkIsingSquareInteriorRadialCell_increment_eq_normSq_full_projection
    n hn (fkIsingSquareRadialPatchCell n m hm i j) s


end
end StatMech.Universality
