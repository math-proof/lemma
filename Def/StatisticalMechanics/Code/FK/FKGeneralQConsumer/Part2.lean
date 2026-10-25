/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.fkc_rqvanhove.Part4
import Theorem.StatisticalMechanics.Code.FK.FKUniqPerEdge.Part3
import Theorem.StatisticalMechanics.Code.FK.FreeWeakLimit.Part8
import Theorem.StatisticalMechanics.Code.FK.MonotoneWeakLimit.Part2
import Theorem.StatisticalMechanics.Code.FK.FKGeneralQConsumer.Part2
open scoped BigOperators
open MeasureTheory Filter Topology SimpleGraph Set

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxHeartbeats 2000000


namespace StatMech.FK

open StatMech.Lattice StatMech.IsingFK ConfigSpace

variable {d : ℕ}


noncomputable def fkgq_freeMass (d N : ℕ) (q : ℝ) (hq : 1 ≤ q) (s : ℝ) :
    ConfigSpace (Sym2 (boxVerts d N)) → ℝ := fun ω =>
  (freeInfiniteVolume d (fsc_logistic_pos s) (fsc_logistic_lt_one s)
      (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d)))).real
    (boxRestrict d N ⁻¹' {ω})


noncomputable def fkgq_wiredMass (d N : ℕ) (q : ℝ) (hq : 1 ≤ q) (s : ℝ) :
    ConfigSpace (Sym2 (boxVerts d N)) → ℝ := fun ω =>
  (wiredInfiniteVolume d (fsc_logistic_pos s) (fsc_logistic_lt_one s)
      (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d)))).real
    (boxRestrict d N ⁻¹' {ω})

end StatMech.FK
