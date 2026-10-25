/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredRootReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCenteredTensorTentRegularity.Part8
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCenteredRootReduction
open Filter Set Topology


namespace StatMech.Universality

noncomputable section

noncomputable def fkIsingExpandingBoundarySquareCenteredRootNode
    (k : Nat) (a b : Fin 2) : Complex :=
  fkIsingSquareBoundaryCenteredRadialPatchFullObservable
      (fkIsingExpandingSquareSide k)
      (fkIsingExpandingSquareSide_pos k)
      ⟨a.1 + (fkIsingExpandingSquareSide k - 1), by
        have ha := a.2
        have hn := fkIsingExpandingSquareSide_pos k
        omega⟩
      ⟨b.1 + (fkIsingExpandingSquareSide k - 1), by
        have hb := b.2
        have hn := fkIsingExpandingSquareSide_pos k
        omega⟩ /
    (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex)


end
end StatMech.Universality
