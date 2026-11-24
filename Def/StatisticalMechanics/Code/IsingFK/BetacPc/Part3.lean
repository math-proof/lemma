module
public import Mathlib
public import Def.StatisticalMechanics.Code.FK.CriticalPoint.Part3
public import Def.StatisticalMechanics.Code.Ising.Magnetization.Part3
public import Theorem.StatisticalMechanics.Code.IsingFK.BetacPc.Part2
open Real


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/BetacPc.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace IsingFK

noncomputable def isingBetaC (d : ℕ) : ℝ :=
  betaC (Ising.magnetization d)


end IsingFK
end StatMech
