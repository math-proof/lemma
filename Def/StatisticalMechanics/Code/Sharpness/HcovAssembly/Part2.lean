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
import Theorem.StatisticalMechanics.Code.Sharpness.HcovAssembly
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


noncomputable def hca_pairSum (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V) (u v : V)
    (P : (↥H.edgeFinset → ℕ) → Prop) : ℝ :=
  ∑' m : ↥H.edgeFinset → ℕ,
    (if P m then (1 : ℝ) else 0) * hca_gap H m A u v * weight H β J (ofEdgeFun H m)


end HcovAssembly
end Sharpness
end StatMech
