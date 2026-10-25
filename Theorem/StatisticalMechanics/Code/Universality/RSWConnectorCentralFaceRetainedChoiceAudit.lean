/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceRetainedChoiceAudit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part46
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceRetainedChoiceAudit
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_rca_radj (i : Fin 9) :
    ((hypercubicLattice 2).induce (rect 0 4 (-2) 2)).Adj
      (rlc_rca_rv i.castSucc) (rlc_rca_rv i.succ) := by
  fin_cases i <;> simp [rlc_rca_rv, hypercubicLattice_adj, Fin.sum_univ_two]

end
end StatMech.Universality
