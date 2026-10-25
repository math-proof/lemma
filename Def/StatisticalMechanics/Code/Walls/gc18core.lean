/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc18core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc16core.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc7core
import Theorem.StatisticalMechanics.Code.Walls.gc6_munonneg
import Theorem.StatisticalMechanics.Code.Ising.HdomNativeWeight.Part3
import Theorem.StatisticalMechanics.Code.Ising.AizenmanSignDominance.Part2
import Theorem.StatisticalMechanics.Code.Ising.TwoReplicaWeighted.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc18core
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.style.openClassical false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Sharpness.FieldGhostDict

open StatMech.Walls.Gc5EqGap StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


def gc18_WeightedPathCrossing (β h : ℝ) (o x y : V) : Prop :=
  ∀ m : ↥(withGhost G).edgeFinset → ℕ,
    sources (withGhost G) (ofEdgeFun (withGhost G) m)
        = ({some o, some x, some y, none} : Finset (Option V)) →
      (∑ K₂ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e},
          (if sources (withGhost G) (ofEdgeFun (withGhost G) K₂.1) = ∅
            then weight (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) K₂.1)
            else 0)
            * (hnw_mass (withGhost G) β (ghostCoupling h β (fun _ => 1))
                  (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e)) ∅
                - hnw_mass (withGhost G) β (ghostCoupling h β (fun _ => 1))
                    (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e)) {some o, none}
                - hnw_mass (withGhost G) β (ghostCoupling h β (fun _ => 1))
                    (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e)) {some o, some x}
                - hnw_mass (withGhost G) β (ghostCoupling h β (fun _ => 1))
                    (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e)) {some o, some y}))
        + 2 * (∑ K₂ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e},
            (if sources (withGhost G) (ofEdgeFun (withGhost G) K₂.1) = {some x, none}
              then weight (withGhost G) β (ghostCoupling h β (fun _ => 1))
                (ofEdgeFun (withGhost G) K₂.1) else 0)
              * hnw_mass (withGhost G) β (ghostCoupling h β (fun _ => 1))
                  (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e)) {some o, none}) ≤ 0


end StatMech.Walls
