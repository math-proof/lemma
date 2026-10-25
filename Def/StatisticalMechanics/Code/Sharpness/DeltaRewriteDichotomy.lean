/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/DeltaRewriteDichotomy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.DeltaRewrite
import Theorem.StatisticalMechanics.Code.Sharpness.SwitchingDichotomy.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.SwitchingCovariance
import Theorem.StatisticalMechanics.Code.Sharpness.DeltaRewriteDichotomy
open Finset BigOperators
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech

namespace Sharpness

open StatMech.Sharpness.RandomCurrent

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι]


noncomputable def drd_pairSum (ends : ι → Sym2 V) (A : Finset V) (F : Finset ι → ℝ)
    (P : Finset ι → Prop) : ℝ :=
  ∑ m ∈ (Finset.univ.powerset.filter (fun m => RandomCurrent.sources ends m = A)),
    (∑ _K ∈ m.powerset.filter (fun K => RandomCurrent.sources ends K = A),
        F m * (if P m then 1 else 0))


end Sharpness
end StatMech
