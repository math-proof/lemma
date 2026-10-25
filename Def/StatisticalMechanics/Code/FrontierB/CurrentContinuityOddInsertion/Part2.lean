/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityOddInsertion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.CurrentContinuityFiniteSwitching
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentContinuityOddInsertion


namespace StatMech.FrontierB

open Finset Sharpness

open scoped symmDiff

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def boundaryPairSummand
    (beta : Real) (interior internalSources exactSecondSources : Finset V)
    (P : Current V -> Prop) [DecidablePred P]
    (pq : EdgeCurrent G × EdgeCurrent G) : Real :=
  (if sources G (ofEdgeFun G pq.1) ∩ interior = internalSources then
      weight G beta (fun _ => 1) (ofEdgeFun G pq.1) else 0) *
    (if sources G (ofEdgeFun G pq.2) = exactSecondSources then
      weight G beta (fun _ => 1) (ofEdgeFun G pq.2) else 0) *
    (if P (ofEdgeFun G (fun e => pq.1 e + pq.2 e)) then 1 else 0)

end StatMech.FrontierB
