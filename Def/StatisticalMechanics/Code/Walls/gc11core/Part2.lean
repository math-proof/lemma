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
import Theorem.StatisticalMechanics.Code.Walls.gc11core
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


def gc11_ClearedSign (β h : ℝ) (o : V) : Prop :=
  ∀ x y : V, o ≠ x → o ≠ y → x ≠ y →
    gc11_Z0 G β h
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
          (({x, y} : Finset V).map someEmb)
    ≤ -2 * (onePt G β h o * onePt G β h x * onePt G β h y) * (gc11_Z0 G β h) ^ 2


end StatMech.Walls
