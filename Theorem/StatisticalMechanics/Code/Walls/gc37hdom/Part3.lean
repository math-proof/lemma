/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc37hdom.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc24deltabridge.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc28ghsrigid
import Theorem.StatisticalMechanics.Code.Walls.ghc_urselleqgap
import Theorem.StatisticalMechanics.Code.Walls.FaithfulnessAudit.Part2
import Theorem.StatisticalMechanics.Code.Ising.CurrentWeight.Part2
import Def.StatisticalMechanics.Code.Walls.gc37hdom.Part3
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

open StatMech.Walls.Gc5EqGap StatMech.Walls.GhcEqGap

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.FieldGhostDict

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem gc37_Z0cubed_triple (β h : ℝ) (o x y : V) :
    (gc15_Z0 G β h) ^ 3 * gc37_triple G β h o x y
      = csG G β h (insert (none : Option V) (({o} : Finset V).map someEmb))
        * csG G β h (insert (none : Option V) (({x} : Finset V).map someEmb))
        * csG G β h (insert (none : Option V) (({y} : Finset V).map someEmb)) := by
  unfold gc37_triple csG
  rw [gc8_eq15_insertion_ghost G β (ghostCoupling h β (fun _ => 1))
        (insert (none : Option V) (({o} : Finset V).map someEmb)),
      gc8_eq15_insertion_ghost G β (ghostCoupling h β (fun _ => 1))
        (insert (none : Option V) (({x} : Finset V).map someEmb)),
      gc8_eq15_insertion_ghost G β (ghostCoupling h β (fun _ => 1))
        (insert (none : Option V) (({y} : Finset V).map someEmb)),
      gc10_moment_ghostSingle G β h o, gc10_moment_ghostSingle G β h x,
      gc10_moment_ghostSingle G β h y]
  unfold gc15_Z0
  ring


theorem gc37_Z0sq_U4 (β h : ℝ) (o x y : V) (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    (gc15_Z0 G β h) ^ 2 * gc37_U4 G β h o x y
      = (gc15_Z0 G β h) * csG G β h (insert (none : Option V) (({o, x, y} : Finset V).map someEmb))
        - csG G β h (insert (none : Option V) (({o} : Finset V).map someEmb))
            * csG G β h (({x, y} : Finset V).map someEmb)
        - csG G β h (({o, x} : Finset V).map someEmb)
            * csG G β h (insert (none : Option V) (({y} : Finset V).map someEmb))
        - csG G β h (({o, y} : Finset V).map someEmb)
            * csG G β h (insert (none : Option V) (({x} : Finset V).map someEmb)) := by
  have hpoly := gc15_u3_currentSum_poly G β h o x y hox hoy hxy
  have hdecomp := gc37_ursell3_eq_U4_add_triple G β h o x y
  have htriple := gc37_Z0cubed_triple G β h o x y
  have hZpos : 0 < gc15_Z0 G β h := gc15_Z0_pos G β h
  have hZne : gc15_Z0 G β h ≠ 0 := ne_of_gt hZpos
  
  rw [hdecomp] at hpoly
  unfold csG
  unfold csG at htriple
  
  
  have key : gc15_Z0 G β h * ((gc15_Z0 G β h) ^ 2 * gc37_U4 G β h o x y)
      = gc15_Z0 G β h *
        ((gc15_Z0 G β h) * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
              (insert (none : Option V) (({o, x, y} : Finset V).map someEmb))
          - currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
              (insert (none : Option V) (({o} : Finset V).map someEmb))
              * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
                  (({x, y} : Finset V).map someEmb)
          - currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
              (({o, x} : Finset V).map someEmb)
              * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
                  (insert (none : Option V) (({y} : Finset V).map someEmb))
          - currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
              (({o, y} : Finset V).map someEmb)
              * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
                  (insert (none : Option V) (({x} : Finset V).map someEmb))) := by
    linear_combination hpoly - 2 * htriple
  exact mul_left_cancel₀ hZne key


end StatMech.Walls
