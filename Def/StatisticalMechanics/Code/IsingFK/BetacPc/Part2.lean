/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/BetacPc.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.FK.CriticalPoint.Part3
import Def.StatisticalMechanics.Code.Ising.Magnetization.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.BetacPc
open Real


namespace StatMech

namespace IsingFK

noncomputable def betaC (mStar : ℝ → ℝ) : ℝ :=
  sSup {β : ℝ | 0 < β ∧ mStar β = 0}

end IsingFK
end StatMech
