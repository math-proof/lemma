/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10ghostfourpoint.lean -/

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
import Theorem.StatisticalMechanics.Code.Ising.AizenmanBarsky.Part5
import Theorem.StatisticalMechanics.Code.Ising.GHSThreePoint
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part10
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc6_ghostgraph
import Theorem.StatisticalMechanics.Code.Walls.gc5_urselleqgap
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option maxHeartbeats 800000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Sharpness.FieldGhostDict

open StatMech.Walls.Gc5EqGap

open StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def eg_ursell4_ghostPlus (β h : ℝ) (o x y : V) : ℝ :=
  expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1))
      (insert (none : Option V) (({o, x, y} : Finset V).map someEmb))
    - expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1)) (({o, x} : Finset V).map someEmb)
        * expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1))
            (insert (none : Option V) (({y} : Finset V).map someEmb))
    - expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1)) (({o, y} : Finset V).map someEmb)
        * expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1))
            (insert (none : Option V) (({x} : Finset V).map someEmb))
    - expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1))
            (insert (none : Option V) (({o} : Finset V).map someEmb))
        * expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1)) (({x, y} : Finset V).map someEmb)


end StatMech.Walls
