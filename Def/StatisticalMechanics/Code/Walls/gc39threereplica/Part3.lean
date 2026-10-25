/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc39threereplica.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc38sharp.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc39threereplica.Part2
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


open StatMech.Sharpness (currentSum)


open StatMech.Sharpness.RandomCurrent (sources connK)


def gc39_ThreeColouringCountIneq {ι W : Type*} [DecidableEq ι] [Fintype ι]
    [DecidableEq W] [Fintype W] (ends : ι → Sym2 W) (o x y g : W) : Prop :=
  #((univ : Finset (Finset ι × Finset ι)).filter (fun p : Finset ι × Finset ι =>
      p.2 ⊆ univ \ p.1
        ∧ sources ends p.1 = ({o, g} : Finset W)
        ∧ sources ends p.2 = ({x, g} : Finset W)
        ∧ sources ends ((univ \ p.1) \ p.2) = ({y, g} : Finset W)))
    ≤ #((univ : Finset (Finset ι × Finset ι)).filter (fun p : Finset ι × Finset ι =>
      p.2 ⊆ univ \ p.1
        ∧ sources ends p.1 = ({o, x, y, g} : Finset W)
        ∧ sources ends p.2 = (∅ : Finset W)
        ∧ sources ends ((univ \ p.1) \ p.2) = (∅ : Finset W)
        ∧ connK ends (p.1 ∪ p.2) o x ∧ connK ends (p.1 ∪ p.2) o y ∧ connK ends (p.1 ∪ p.2) o g))

end StatMech.Walls
