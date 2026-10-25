/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/MaximalErgodicGarsia.lean -/

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

namespace GarsiaMax

variable {α : Type*} {T : α → α} {f : α → ℝ}


noncomputable def maxPartialSum (T : α → α) (f : α → ℝ) (N : ℕ) (hN : 1 ≤ N) (x : α) : ℝ :=
  (Finset.Icc 1 N).sup' (by rw [Finset.nonempty_Icc]; exact hN)
    (fun n => birkhoffSum T f n x)


end GarsiaMax
end StatMech
