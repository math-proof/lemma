module
public import Theorem.StatisticalMechanics.Code.OSSS.Integration.Part2
public import Theorem.StatisticalMechanics.Code.OSSS.BetaThresholdBound
public import Theorem.StatisticalMechanics.Code.FK.WiredDomChain.Part4
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.NumberTheory.Harmonic.Bounds
open scoped BigOperators
open Filter Topology Real Finset
set_option linter.style.longLine false


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LogCesaroLimit.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace OSSS

namespace LogCesaroLimit

open BetaThresholdBound


noncomputable def harmonicReal (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.Ico 1 (n + 1), 1 / (i : ℝ)

end LogCesaroLimit
end OSSS
end StatMech
