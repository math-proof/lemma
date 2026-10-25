/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalPairedConnection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutSquareEmbedding.Part6
open MeasureTheory SimpleGraph StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

def FKRectPrimalUnexploredConnectionEvent
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration)
    (source target : FKRectPrimalUnexploredVertex R S eta) :
    Set (ConfigSpace
      (Sym2 (FKRectPrimalUnexploredVertex R S eta))) :=
  {omega |
    (FK.openSub (fkRectPrimalUnexploredInducedGraph R S eta) omega).Reachable
      source target}

end
end StatMech.FrontierD
