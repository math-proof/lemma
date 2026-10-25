/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/BetaThresholdBound.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.IntegrationSubcriticalAssembly
import Theorem.StatisticalMechanics.Code.OSSS.FKSharpDiffIneq
open scoped BigOperators
open Real Filter Topology Set Finset

set_option linter.style.longLine false
set_option linter.unusedVariables false


namespace StatMech

namespace OSSS.BetaThresholdBound

open StatMech.OSSS.IntegrationSubcritical


noncomputable def logRatio (Sg : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.log (Sg n) / Real.log (n : ℝ)


def thresholdSet (Sgf : ℝ → ℕ → ℝ) : Set ℝ :=
  {β | 1 ≤ Filter.limsup (logRatio (Sgf β)) atTop}


noncomputable def beta1 (Sgf : ℝ → ℕ → ℝ) : ℝ := sInf (thresholdSet Sgf)


end OSSS.BetaThresholdBound
end StatMech
