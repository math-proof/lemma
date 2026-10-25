/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentConditional.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentParityLift.Part2
open MeasureTheory
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def conditionalCurrentTerm (beta : ℝ) (k : ℕ) : ℝ :=
  beta ^ k / k.factorial

noncomputable def parityEdgeKernel (beta : ℝ) (odd : Bool) (k : ℕ) : ℝ :=
  if odd then
    if Odd k then conditionalCurrentTerm beta k / Real.sinh beta else 0
  else
    if Even k then conditionalCurrentTerm beta k / Real.cosh beta else 0

noncomputable def parityCurrentKernel (beta : ℝ)
    (H : Finset (Sym2 V)) (m : EdgeCurrent G) : ℝ :=
  ∏ e : G.edgeFinset, parityEdgeKernel beta (e.1 ∈ H) (m e)

end StatMech.FrontierB
