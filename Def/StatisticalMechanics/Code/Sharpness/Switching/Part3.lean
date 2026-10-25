/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Switching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.Switching.Part2
open Finset BigOperators
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false


namespace StatMech

namespace Sharpness

namespace RandomCurrent

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι]


noncomputable def compOf (ends : ι → Sym2 V) (K : Finset ι) (u : V) : Finset V :=
  (Finset.univ : Finset V).filter (fun x => connK ends K u x)

end RandomCurrent
end Sharpness
end StatMech
