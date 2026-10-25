/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc20closure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc19switching.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc18core.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc16core.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc15core.Part5
import Theorem.StatisticalMechanics.Code.Walls.gc7core
import Theorem.StatisticalMechanics.Code.Walls.gc6_munonneg
import Theorem.StatisticalMechanics.Code.Ising.HdomNativeWeight.Part3
import Theorem.StatisticalMechanics.Code.Ising.AizenmanSignDominance.Part2
import Theorem.StatisticalMechanics.Code.Ising.TwoReplicaWeighted.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc20closure
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Sharpness.FieldGhostDict

open StatMech.Walls.Gc5EqGap StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


def gc20_FiberConnRegime (β h : ℝ) (o x y : V) (m : ↥(withGhost G).edgeFinset → ℕ) : Prop :=
  
  ((∀ K₁ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e},
      sources (withGhost G) (ofEdgeFun (withGhost G) K₁.1) = ∅ →
      connP (oddEdges (withGhost G).edgeFinset
          (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) (some o) none)
    ∧ (∀ K₁ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e},
        sources (withGhost G) (ofEdgeFun (withGhost G) K₁.1) = ∅ →
        connP (oddEdges (withGhost G).edgeFinset
            (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) (some o) (some x))
    ∧ (∀ K₁ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e},
        sources (withGhost G) (ofEdgeFun (withGhost G) K₁.1) = ∅ →
        connP (oddEdges (withGhost G).edgeFinset
            (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) (some o) (some y))
    ∧ (∀ K₂ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e},
        sources (withGhost G) (ofEdgeFun (withGhost G) K₂.1) = {some x, none} →
        connP (oddEdges (withGhost G).edgeFinset
            (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e))) (some o) none)
    ∧ (∀ K₁ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e},
        sources (withGhost G) (ofEdgeFun (withGhost G) K₁.1) = ∅ →
        connP (oddEdges (withGhost G).edgeFinset
            (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) (some x) none))
  ∨ 
  (¬ connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) m)) (some o) none
    ∧ ¬ connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) m)) (some o) (some y)
    ∧ (∀ K₂ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e},
        sources (withGhost G) (ofEdgeFun (withGhost G) K₂.1) = ∅ →
        connP (oddEdges (withGhost G).edgeFinset
            (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e))) (some o) (some x)))
  ∨ 
  (¬ connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) m)) (some o) none
    ∧ ¬ connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) m)) (some o) (some x)
    ∧ (∀ K₂ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e},
        sources (withGhost G) (ofEdgeFun (withGhost G) K₂.1) = ∅ →
        connP (oddEdges (withGhost G).edgeFinset
            (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e))) (some o) (some y)))


end StatMech.Walls
