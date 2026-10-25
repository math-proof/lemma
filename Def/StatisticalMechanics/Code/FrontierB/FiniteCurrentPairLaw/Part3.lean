/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentPairLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FiniteNormalizedSwitching
import Theorem.StatisticalMechanics.Code.Sharpness.DeltaBound.Part2
import Instance.StatisticalMechanics.Code.FrontierB.FiniteCurrentPairLaw
open MeasureTheory
open scoped ENNReal symmDiff


namespace StatMech.FrontierB

open Finset Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def sourcePairRealSummand
    (beta : ℝ) (J : Sym2 V → ℝ) (A B : Finset V)
    (P : Current V → Prop) [DecidablePred P]
    (pq : EdgeCurrent G × EdgeCurrent G) : ℝ :=
  (if sources G (ofEdgeFun G pq.1) = A then
      weight G beta J (ofEdgeFun G pq.1) else 0) *
    (if sources G (ofEdgeFun G pq.2) = B then
      weight G beta J (ofEdgeFun G pq.2) else 0) *
    (if P (ofEdgeFun G (fun e => pq.1 e + pq.2 e)) then 1 else 0)

end StatMech.FrontierB
