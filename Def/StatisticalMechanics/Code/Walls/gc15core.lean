/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc15core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.MultiReplica.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc10ghostfourpoint
import Theorem.StatisticalMechanics.Code.Walls.gc8Z0pos
import Theorem.StatisticalMechanics.Code.Walls.gc15core
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Sharpness.FieldGhostDict

open StatMech.Walls.Gc5EqGap StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


variable (S : SimpleGraph V) [DecidableRel S.Adj]


noncomputable def gc15_tpsum (β : ℝ) (J : Sym2 V → ℝ) (m : ↥S.edgeFinset → ℕ) (A B : Finset V) : ℝ :=
  ∑ K : {pq : (↥S.edgeFinset → ℕ) × (↥S.edgeFinset → ℕ) // ∀ e, pq.1 e + pq.2 e ≤ m e},
    (if sources S (ofEdgeFun S K.1.1) = A then weight S β J (ofEdgeFun S K.1.1) else 0)
      * (if sources S (ofEdgeFun S K.1.2) = B then weight S β J (ofEdgeFun S K.1.2) else 0)
      * weight S β J (ofEdgeFun S (fun e => m e - K.1.1 e - K.1.2 e))


noncomputable def gc15_tFiber (β : ℝ) (J : Sym2 V → ℝ) (A B C : Finset V)
    (m : ↥S.edgeFinset → ℕ) : ℝ :=
  if sources S (ofEdgeFun S m) = A ∆ B ∆ C then gc15_tpsum S β J m A B else 0


end StatMech.Walls
