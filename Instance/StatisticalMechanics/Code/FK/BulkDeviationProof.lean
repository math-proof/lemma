/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BulkDeviationProof.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.UniformBulkDeviation.Part2
import Theorem.StatisticalMechanics.Code.FK.FKLimitsClose.Part3
import Def.StatisticalMechanics.Code.FK.BulkDeviationProof
open MeasureTheory Filter Topology SimpleGraph Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.style.openClassical false
set_option linter.style.longLine false


namespace StatMech

namespace FK

variable {d : ℕ}


section FreeAbstract

variable {Vin Vout : Type*} [Fintype Vin] [DecidableEq Vin] [Fintype Vout] [DecidableEq Vout]

variable {Gin : SimpleGraph Vin} [DecidableRel Gin.Adj]

variable {Gout : SimpleGraph Vout} [DecidableRel Gout.Adj]

variable {ιV : Vin → Vout}


instance : DecidablePred (bdp_noBdry (Vout := Vout)) := fun _ => instDecidableFalse


end FreeAbstract
end FK
end StatMech
