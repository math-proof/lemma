/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentConditional.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentParityLift.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentConditional
open MeasureTheory
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def parityFiberMass (G : SimpleGraph V) [DecidableRel G.Adj] (beta : ℝ)
    (H : Finset (Sym2 V)) : ℝ :=
  ∏ e : G.edgeFinset,
    if e.1 ∈ H then Real.sinh beta else Real.cosh beta

end StatMech.FrontierB
