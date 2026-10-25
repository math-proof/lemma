/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc41split.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc40count.Part5
import Theorem.StatisticalMechanics.Code.Walls.gc41split.Part2
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Walls.Gc5EqGap StatMech.Walls.GhcEqGap

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.FieldGhostDict

open StatMech.Sharpness.RandomCurrent (sources connK degK compOf switching_card
  exists_conn_set sources_symmDiff path_exists mem_sources)

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def gc41_allConnTripleSum (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V) (o x y g : V) : ℝ :=
  ∑' z : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ),
    ((if sources G (ofEdgeFun G z.1) = A then weight G β J (ofEdgeFun G z.1) else 0)
      * (if sources G (ofEdgeFun G z.2.1) = (∅ : Finset V) then weight G β J (ofEdgeFun G z.2.1) else 0)
      * (if sources G (ofEdgeFun G z.2.2) = (∅ : Finset V) then weight G β J (ofEdgeFun G z.2.2) else 0))
      * (if CurrentConnected G (ofEdgeFun G (fun e => z.1 e + z.2.1 e)) o x
            ∧ CurrentConnected G (ofEdgeFun G (fun e => z.1 e + z.2.1 e)) o y
            ∧ CurrentConnected G (ofEdgeFun G (fun e => z.1 e + z.2.1 e)) o g then 1 else 0)


end StatMech.Walls
