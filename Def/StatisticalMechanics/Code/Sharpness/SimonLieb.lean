/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SimonLieb.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part10
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneProps.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.ClaimIsingFull.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.IsingSharpnessFull.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.SimonLieb
open SimpleGraph Finset
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000


namespace StatMech

namespace Sharpness

section SimonWeight

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def simonWeight (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V) (o : V) :
    V → V → ℝ :=
  fun x y => Real.tanh (β * J s(x, y)) * expectationJ G β (couplingIn J S) {o, x}


end SimonWeight
end Sharpness
end StatMech
