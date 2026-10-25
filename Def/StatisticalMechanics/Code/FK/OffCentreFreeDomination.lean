/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreFreeDomination.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.OffCentreDomination.Part13
import Theorem.StatisticalMechanics.Code.FK.OffCentreFreeDomination
open scoped BigOperators
open SimpleGraph


namespace StatMech.FK

noncomputable section

variable {Vin Vout : Type*}

variable [Fintype Vin] [DecidableEq Vin]

variable [Fintype Vout] [DecidableEq Vout]

variable (Gin : SimpleGraph Vin) [DecidableRel Gin.Adj]

variable (Gout : SimpleGraph Vout) [DecidableRel Gout.Adj]

variable (iota : Vin -> Vout)

def falseBoundary (_ : Vout) : Prop := False

end
end StatMech.FK
