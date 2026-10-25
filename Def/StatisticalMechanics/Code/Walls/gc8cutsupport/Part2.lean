/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8cutsupport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part10
import Theorem.StatisticalMechanics.Code.Ising.CurrentWeight.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc8cutsupport
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option maxHeartbeats 800000


namespace StatMech.Walls

open StatMech.Ising StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


def gc8_cutSupportDecomp (S : Finset V) (n₁ n₂ : Ising.Current V) : Prop :=
  (∀ e ∈ G.edgeFinset, ¬ gc8Crosses S e)
    ∧ (∀ e ∈ G.edgeFinset,
        n₁ e = acwRestrict (acwInternal S) n₁ e + acwRestrict (acwInternal Sᶜ) n₁ e
          ∧ n₂ e = acwRestrict (acwInternal S) n₂ e + acwRestrict (acwInternal Sᶜ) n₂ e)
    ∧ (Sharpness.sources G (acwRestrict (acwInternal S) n₁) = S ∩ Sharpness.sources G n₁
        ∧ Sharpness.sources G (acwRestrict (acwInternal S) n₂) = S ∩ Sharpness.sources G n₂)


end StatMech.Walls
