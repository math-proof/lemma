/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/SourceCurrentTail.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.LocalCurrentTail.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.Claim1IsingComplete.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.HighTempSwitching.Part4
import Theorem.StatisticalMechanics.Code.FrontierB.SourceCurrentTail.Part2
open MeasureTheory
open scoped ENNReal BigOperators


namespace StatMech.FrontierB

open Sharpness Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def pathCorrelationConstant {u v : V}
    (beta : ℝ) (J : Sym2 V → ℝ) (S : Finset V)
    (p : G.Walk u v) : ℝ :=
  weight G beta (couplingIn J S) (ofEdgeFun G (pathEdgeCurrent G p)) /
    Real.exp (∑ e ∈ G.edgeFinset, beta * couplingIn J S e)


end StatMech.FrontierB
