/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptivePairedConnection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalAdaptiveProjection.Part9
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalPairedConnection
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalAdaptivePairedConnection.Part2
open MeasureTheory SimpleGraph StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

def FKRectPrimalFullDistinctPairedWitness
    (R : FKRectTorus) (pair : Fin R.height -> Fin R.height)
    (S : Finset (Fin R.height)) (rho : ConfigSpace (Sym2 R.Vertex)) : Prop :=
  (∀ i ∈ S,
    (FK.openSub (fkRectCutGraph R) rho).Reachable
      (fkRectLeftColumn R, i) (fkRectRightColumn R, pair i)) ∧
  (∀ i ∈ S, ∀ j ∈ S, i ≠ j ->
    ¬ (FK.openSub (fkRectCutGraph R) rho).Reachable
      (fkRectLeftColumn R, i) (fkRectLeftColumn R, j))

end
end StatMech.FrontierD
