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
import Abbrev.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge
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


def endsM (m : ↥G.edgeFinset → ℕ) : Copy G m → Sym2 V := fun i => i.1.1


noncomputable def profileFlux (m : ↥G.edgeFinset → ℕ) (S : Finset (Copy G m)) :
    ↥G.edgeFinset → ℕ :=
  fun e => #(S.filter (fun i : Copy G m => i.1 = e))

end FluxEdgeCopy
end Sharpness
end StatMech
