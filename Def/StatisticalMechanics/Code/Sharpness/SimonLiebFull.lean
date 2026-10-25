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


noncomputable def ssl_backboneClassSum (β : ℝ) (J : Sym2 V → ℝ) (x y : V)
    {ι : Type*} (sel : (↥G.edgeFinset → ℕ) → ι) (i : ι) : ℝ :=
  ∑' m : ↥G.edgeFinset → ℕ,
    if sources G (ofEdgeFun G m) = {x, y} ∧ sel m = i
      then weight G β J (ofEdgeFun G m) else 0


end Sharpness
end StatMech
