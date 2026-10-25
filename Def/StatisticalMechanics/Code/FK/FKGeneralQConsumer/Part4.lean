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
import Theorem.StatisticalMechanics.Code.FK.FKGeneralQConsumer.Part4
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


noncomputable def fkgq_freeDelta (N : ℕ) (e : Sym2 (boxVerts d N))
    (q t : ℝ) (n : ℕ) : ℝ :=
  ∑ dir : Fin d × Bool,
    |freeEdgeDensity d q (edgeIncl d N e) (fsc_logistic t) - fkgq_unitMarg d q n dir t|


noncomputable def fkgq_wiredDelta (N : ℕ) (e : Sym2 (boxVerts d N))
    (q t : ℝ) (n : ℕ) : ℝ :=
  ∑ dir : Fin d × Bool,
    |fkgq_unitWiredMarg d q n dir t
      - wiredEdgeDensity d q (edgeIncl d N e) (fsc_logistic t)|

end StatMech.FK
