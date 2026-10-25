/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanBarsky.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.GHSFull.Part3
import Theorem.StatisticalMechanics.Code.Ising.AizenmanBarsky.Part2
open scoped BigOperators symmDiff
open Finset SimpleGraph Set

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech

namespace Ising

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def ghsBoundSym (β h : ℝ) (o : V) (e : Sym2 V) : ℝ :=
  Sym2.lift ⟨fun x y => cov2 G β h o x * onePt G β h y + cov2 G β h o y * onePt G β h x,
    fun a b => by ring⟩ e

end Ising
end StatMech
