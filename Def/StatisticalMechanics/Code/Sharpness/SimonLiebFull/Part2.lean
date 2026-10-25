/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SimonLiebFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part10
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneProps.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.SimonLieb.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.ClaimIsingFull.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.IsingSharpnessFull.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.SimonLiebFull
open SimpleGraph Finset
open scoped BigOperators Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000


namespace StatMech

namespace Sharpness

open Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def ssl_backboneWeight (β : ℝ) (J : Sym2 V → ℝ) (x y : V)
    {ι : Type*} (sel : (↥G.edgeFinset → ℕ) → ι) (i : ι) : ℝ :=
  ssl_backboneClassSum G β J x y sel i / currentSum G β J ∅


end Sharpness
end StatMech
