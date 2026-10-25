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
open Real


namespace StatMech

namespace IsingFK

noncomputable def pToBeta (q p : ℝ) : ℝ := -((q - 1) / q) * Real.log (1 - p)


noncomputable def betaToP (q β : ℝ) : ℝ := 1 - Real.exp (-(q / (q - 1)) * β)


end IsingFK
end StatMech
