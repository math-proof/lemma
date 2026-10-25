/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/RussoFormula.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.PivotalFactor


namespace StatMech

namespace Percolation

open ConfigSpace Function Finset StatMech StatMech.Sharpness

variable {E : Type*} [Fintype E] [DecidableEq E]


noncomputable def rus_openCount (ω : ConfigSpace E) : ℝ := ∑ e, openInd ω e


noncomputable def rus_expect (p : ℝ) (f : ConfigSpace E → ℝ) : ℝ :=
  ∑ ω, f ω * configWeight p ω


end Percolation
end StatMech
