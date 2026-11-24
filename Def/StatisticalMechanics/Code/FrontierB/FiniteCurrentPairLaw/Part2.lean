module
public import Theorem.StatisticalMechanics.Code.FrontierB.FiniteNormalizedSwitching
public import Theorem.StatisticalMechanics.Code.Sharpness.DeltaBound.Part2
public import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentPairLaw
open MeasureTheory
open scoped ENNReal symmDiff


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentPairLaw.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierB

open Finset Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


def sourcePairSuperpositionEvent
    (P : Current V → Prop) : Set (EdgeCurrent G × EdgeCurrent G) :=
  {pq | P (ofEdgeFun G (fun e => pq.1 e + pq.2 e))}

end StatMech.FrontierB
