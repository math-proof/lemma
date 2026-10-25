/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FluxEdgeCopyBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.Switching.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part10
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part2
open Finset BigOperators
open scoped symmDiff Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech

namespace Sharpness

namespace FluxEdgeCopy

variable {E : Type*} [Fintype E] [DecidableEq E] {β : E → Type*}
  [∀ e, Fintype (β e)] [∀ e, DecidableEq (β e)]


open StatMech.Sharpness (ofEdgeFun)

open StatMech.Sharpness.RandomCurrent (degK adjStep connK)

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def sourcePairDisconnSum (β : ℝ) (J : Sym2 V → ℝ) (A B : Finset V) (u v : V) : ℝ :=
  ∑' pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ),
    ((if sources G (ofEdgeFun G pq.1) = A then weight G β J (ofEdgeFun G pq.1) else 0)
        * (if sources G (ofEdgeFun G pq.2) = B then weight G β J (ofEdgeFun G pq.2) else 0))
      * (if ¬ CurrentConnected G (ofEdgeFun G (fun e => pq.1 e + pq.2 e)) u v then 1 else 0)


end FluxEdgeCopy
end Sharpness
end StatMech
