/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc11core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc10eq15
import Theorem.StatisticalMechanics.Code.Walls.gc10ghostfourpoint
import Theorem.StatisticalMechanics.Code.Walls.gc10core
import Theorem.StatisticalMechanics.Code.Ising.CorrelationRatio
import Def.StatisticalMechanics.Code.Walls.gc11core
open Finset BigOperators SimpleGraph
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Sharpness.FieldGhostDict

open StatMech.Walls.Gc5EqGap

open StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem gc11_Z0_pos (β h : ℝ) : 0 < gc11_Z0 G β h :=
  gc10_eq15_currentMass_pos G β (ghostCoupling h β (fun _ => 1))


theorem gc11_cleared (β h : ℝ) (o x y : V) :
    eg_ursell4_ghostPlus G β h o x y * (gc11_Z0 G β h) ^ 2
      = gc11_Z0 G β h
          * Sharpness.currentSum (withGhost G) β (gc11_Jghost β h)
              (insert (none : Option V) (({o, x, y} : Finset V).map someEmb))
        - Sharpness.sourcePairSum (withGhost G) β (gc11_Jghost β h)
            (({o, x} : Finset V).map someEmb)
            (insert (none : Option V) (({y} : Finset V).map someEmb))
        - Sharpness.sourcePairSum (withGhost G) β (gc11_Jghost β h)
            (({o, y} : Finset V).map someEmb)
            (insert (none : Option V) (({x} : Finset V).map someEmb))
        - Sharpness.sourcePairSum (withGhost G) β (gc11_Jghost β h)
            (insert (none : Option V) (({o} : Finset V).map someEmb))
            (({x, y} : Finset V).map someEmb) := by
  unfold eg_ursell4_ghostPlus gc11_Z0 gc11_Jghost
  rw [Sharpness.sourcePairSum_eq_mul, Sharpness.sourcePairSum_eq_mul,
      Sharpness.sourcePairSum_eq_mul]
  rw [gc10_eq15_ghost G β _ (insert (none : Option V) (({o, x, y} : Finset V).map someEmb)),
      gc10_eq15_ghost G β _ (({o, x} : Finset V).map someEmb),
      gc10_eq15_ghost G β _ (insert (none : Option V) (({y} : Finset V).map someEmb)),
      gc10_eq15_ghost G β _ (({o, y} : Finset V).map someEmb),
      gc10_eq15_ghost G β _ (insert (none : Option V) (({x} : Finset V).map someEmb)),
      gc10_eq15_ghost G β _ (insert (none : Option V) (({o} : Finset V).map someEmb)),
      gc10_eq15_ghost G β _ (({x, y} : Finset V).map someEmb)]
  ring


theorem gc11_triple_Z0cube_eq (β h : ℝ) (o x y : V) :
    (onePt G β h o * onePt G β h x * onePt G β h y) * (gc11_Z0 G β h) ^ 3
      = Sharpness.currentSum (withGhost G) β (gc11_Jghost β h)
            (insert (none : Option V) (({o} : Finset V).map someEmb))
        * Sharpness.currentSum (withGhost G) β (gc11_Jghost β h)
            (insert (none : Option V) (({x} : Finset V).map someEmb))
        * Sharpness.currentSum (withGhost G) β (gc11_Jghost β h)
            (insert (none : Option V) (({y} : Finset V).map someEmb)) := by
  unfold onePt gc11_Z0 gc11_Jghost
  rw [gc10_eq15_magnetization, gc10_eq15_magnetization, gc10_eq15_magnetization]
  ring


end StatMech.Walls
