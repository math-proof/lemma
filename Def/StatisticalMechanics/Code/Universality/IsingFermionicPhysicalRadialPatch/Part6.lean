/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialRectangle.Part6
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalDirichletLimit.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialPatch.Part5


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open Filter Set Topology

noncomputable section

noncomputable def fkIsingSquareRadialPatchFullObservable
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (i j : Fin m) : Complex :=
  fkIsingSquareWiredFullMedialObservable n hn
    (fkIsingSquareRadialPatchEdge n m hm i j)

end
end StatMech.Universality
