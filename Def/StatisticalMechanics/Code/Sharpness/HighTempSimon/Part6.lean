/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSimon.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.HighTempSwitching.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.HighTempSimon.Part3
open Finset SimpleGraph
open scoped BigOperators symmDiff


namespace StatMech

namespace Sharpness

open Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def highTempSwitchMap (S : Finset V) (o z : V)
    (ho : o ∈ S) (hz : z ∉ S) :
    ↥(highTempSwitchInputs G S o z) → ↥(highTempSwitchOutputs G S o z) :=
  fun p => ⟨highTempSwitch G S o z ho hz p.1 (by
      have h := p.2
      change p.1 ∈ Finset.univ.filter
        (HighTempSwitchInput.Valid G S o z) at h
      exact (Finset.mem_filter.mp h).2),
    highTempSwitch_mem_outputs G S o z ho hz p.1 p.2⟩


end Sharpness
end StatMech
