/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentConditionalPMF.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentConditional.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentConditionalPMF.Part5
open MeasureTheory
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

section Ambient

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def complementParityKernel
    (beta : ℝ) (H : Finset (Sym2 V)) (S : Finset G.edgeFinset)
    (b : {e : G.edgeFinset // e ∉ S} → ℕ) : ℝ :=
  ∏ e, parityEdgeKernel beta (e.1.1 ∈ H) (b e)

end Ambient
end StatMech.FrontierB
