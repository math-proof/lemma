/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LogCesaroLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.Integration.Part2
import Theorem.StatisticalMechanics.Code.OSSS.BetaThresholdBound
import Theorem.StatisticalMechanics.Code.FK.WiredDomChain.Part4
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.Bounds
import Theorem.StatisticalMechanics.Code.OSSS.LogCesaroLimit
open scoped BigOperators
open Filter Topology Real Finset

set_option linter.style.longLine false


namespace StatMech

namespace OSSS

namespace LogCesaroLimit

open BetaThresholdBound


noncomputable def logCesaro (u : ℕ → ℝ) (n : ℕ) : ℝ :=
  (1 / Real.log (n : ℝ)) * ∑ i ∈ Finset.Ico 1 (n + 1), u i / (i : ℝ)

end LogCesaroLimit
end OSSS
end StatMech
