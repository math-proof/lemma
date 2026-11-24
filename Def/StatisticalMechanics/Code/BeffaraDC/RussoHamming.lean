module
public import Theorem.StatisticalMechanics.Code.BeffaraDC.RussoInfluence.Part2
public import Theorem.StatisticalMechanics.Code.BeffaraDC.Hamming
public import Theorem.StatisticalMechanics.Code.Inequalities.FKG


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/RussoHamming.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace BeffaraDC

open ConfigSpace Function Finset

variable {E : Type*} [Fintype E] [DecidableEq E]


noncomputable def expect (p : ℝ) (f : ConfigSpace E → ℝ) : ℝ :=
  ∑ ω, f ω * configWeight p ω


end BeffaraDC
end StatMech
