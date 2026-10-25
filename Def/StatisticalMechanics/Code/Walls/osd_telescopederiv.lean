/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/osd_telescopederiv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.OSSS.Integration.Part2
open scoped BigOperators
open Real Set Finset

set_option linter.style.longLine false


namespace StatMech

namespace Walls

noncomputable def osd_meanLogTerm (fseq : ℕ → ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (1 / Real.log n) * ∑ i ∈ Finset.Ico 1 (n + 1), fseq i x / (i : ℝ)


end Walls
end StatMech
