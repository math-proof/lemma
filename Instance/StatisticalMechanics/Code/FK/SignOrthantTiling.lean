/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SignOrthantTiling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.BoxTiling.Part2
import Theorem.StatisticalMechanics.Code.FK.FKInterfaceSubadd.Part2
import Theorem.StatisticalMechanics.Code.FK.FKUniqPrimitives
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Abbrev.StatisticalMechanics.Code.FK.SignOrthantTiling
open MeasureTheory Set Filter Topology Real
open scoped BigOperators
open SimpleGraph

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option maxHeartbeats 1000000


namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice


instance sot_instFintypeRepSum (V : Type) [Fintype V] : (k : ℕ) → Fintype (sot_RepSum V k)
  | 0 => inferInstanceAs (Fintype PEmpty)
  | (k + 1) => @instFintypeSum V (sot_RepSum V k) _ (sot_instFintypeRepSum V k)

instance sot_instDecidableEqRepSum (V : Type) [DecidableEq V] :
    (k : ℕ) → DecidableEq (sot_RepSum V k)
  | 0 => inferInstanceAs (DecidableEq PEmpty)
  | (k + 1) => @instDecidableEqSum V (sot_RepSum V k) _ (sot_instDecidableEqRepSum V k)


end FK
end StatMech
