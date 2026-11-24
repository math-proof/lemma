module
public import Theorem.StatisticalMechanics.Code.Inequalities.Russo
public import Theorem.StatisticalMechanics.Code.BeffaraDC.RussoInfluence


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/RussoInfluence.lean -/
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


noncomputable def influence (p : ℝ) (A : Set (ConfigSpace E)) (e : E) : ℝ :=
  pivotalProb p A e


end BeffaraDC
end StatMech
