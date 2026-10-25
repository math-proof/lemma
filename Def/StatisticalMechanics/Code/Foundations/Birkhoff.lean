/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Birkhoff.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
open MeasureTheory Filter Finset Function
open scoped Topology


namespace StatMech

namespace Birkhoff

variable {α : Type*} {T : α → α} {f : α → ℝ}


noncomputable def maxBirkhoff (T : α → α) (f : α → ℝ) (n : ℕ) (x : α) : ℝ :=
  (Finset.range (n + 1)).sup' (Finset.nonempty_range_iff.mpr n.succ_ne_zero)
    (fun k => birkhoffSum T f k x)


end Birkhoff
end StatMech
