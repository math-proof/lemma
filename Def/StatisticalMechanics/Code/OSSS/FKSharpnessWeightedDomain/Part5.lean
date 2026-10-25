/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedDomain.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedPeriodic.Part3
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedDomain.Part4
open scoped BigOperators Classical
open Finset Set

set_option linter.unusedSectionVars false


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

variable (C : SimpleGraph V) [DecidableRel C.Adj]


variable {Vin Vout : Type*} [Fintype Vin] [Fintype Vout]

variable [DecidableEq Vin] [DecidableEq Vout]

variable (Gin : SimpleGraph Vin) [DecidableRel Gin.Adj]

variable (Gout : SimpleGraph Vout) [DecidableRel Gout.Adj]

variable (iota : Vin -> Vout)

variable (bdryOut : Vout -> Prop) [DecidablePred bdryOut]


noncomputable def ocd_psiShiftW (pfOut : Sym2 Vout -> Real)
    (psi : ConfigSpace (Sym2 Vout)) (q : Real) : Real :=
  ocd_psiEdgeFactorW Gout iota pfOut psi *
    q ^ ocd_outsideShift Gout iota bdryOut psi

end FK
end StatMech
