/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc38sharp.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc37hdom.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc38sharp
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

open StatMech.Sharpness (ofEdgeFun weight currentSum sourcePairSum)

open StatMech.Sharpness.FluxEdgeCopy (Copy endsM endsM_not_isDiag sourcePairDisconnSum
  sourcePairDisconnSum_eq_edgecopy sourcePairSum_eq_edgecopy)


noncomputable def gc38_sourcePairAllConnSum (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V)
    (o x y g : V) : ℝ :=
  ∑' pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ),
    ((if sources G (ofEdgeFun G pq.1) = A then weight G β J (ofEdgeFun G pq.1) else 0)
        * (if sources G (ofEdgeFun G pq.2) = (∅ : Finset V) then weight G β J (ofEdgeFun G pq.2) else 0))
      * (if CurrentConnected G (ofEdgeFun G (fun e => pq.1 e + pq.2 e)) o x
            ∧ CurrentConnected G (ofEdgeFun G (fun e => pq.1 e + pq.2 e)) o y
            ∧ CurrentConnected G (ofEdgeFun G (fun e => pq.1 e + pq.2 e)) o g then 1 else 0)


end StatMech.Walls
