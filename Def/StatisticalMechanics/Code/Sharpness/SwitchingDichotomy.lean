/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SwitchingDichotomy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import Theorem.StatisticalMechanics.Code.Sharpness.Switching.Part3

@[expose] public section

open Finset BigOperators
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech

namespace Sharpness

namespace RandomCurrent

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι]


noncomputable def compOddVertices (ends : ι → Sym2 V) (m : Finset ι) (u : V) : Finset V :=
  (compOf ends m u).filter (fun x => Odd (degK ends m x))

end RandomCurrent
end Sharpness
end StatMech
