/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceRetainedChoiceAudit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part46
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceRetainedChoiceAudit.Part2
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_rca_ladj (i : Fin 10) :
    ((hypercubicLattice 2).induce (rect (-4) 0 (-2) 2)).Adj
      (rlc_rca_lv i.castSucc) (rlc_rca_lv i.succ) := by
  fin_cases i <;> simp [rlc_rca_lv, hypercubicLattice_adj, Fin.sum_univ_two]

end
end StatMech.Universality
