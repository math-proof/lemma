/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Switching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Sharpness.Switching
open Finset BigOperators
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false


namespace StatMech

namespace Sharpness

namespace RandomCurrent

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι]


@[simp] lemma mem_sources {ends : ι → Sym2 V} {T : Finset ι} {x : V} :
    x ∈ sources ends T ↔ Odd (degK ends T x) := by
  simp [sources]


end RandomCurrent
end Sharpness
end StatMech
