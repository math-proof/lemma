/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HcovAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.DeltaRewriteDichotomy.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyDischarge
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
import Theorem.StatisticalMechanics.Code.Ising.CorrelationRatio
import Def.StatisticalMechanics.Code.Sharpness.HcovAssembly.Part3
open Finset BigOperators SimpleGraph
open scoped symmDiff Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000


namespace StatMech

namespace Sharpness

namespace HcovAssembly

open StatMech.Sharpness (ofEdgeFun weight currentSum)

open StatMech.Sharpness.FluxEdgeCopy (Copy endsM endsM_not_isDiag sourcePairDisconnSum
  sourcePairDisconnSum_eq_switching_gap)

open StatMech.Sharpness.RandomCurrent (connK switching_disconnect_card)

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (H : SimpleGraph V) [DecidableRel H.Adj]


open StatMech.Ising (isingExpectation spinProd)

open StatMech.Sharpness.FieldGhostDict (ghostCoupling someEmb
  fgd_ghostCurrentRep_unconditional fgd_isingExpectation_eq_currentSum_ratio
  fgd_isingExpectation_eq_currentSum_ratio_odd someEmb_apply)

variable (G : SimpleGraph V) [DecidableRel G.Adj]


@[simp] theorem hcaBondSource_mk (o x y : V) :
    hcaBondSource o s(x, y) = insert none ((({o} : Finset V) ∆ {x, y}).map someEmb) := rfl


end HcovAssembly
end Sharpness
end StatMech
