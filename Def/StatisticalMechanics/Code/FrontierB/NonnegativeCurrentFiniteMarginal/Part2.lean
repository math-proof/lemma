/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/NonnegativeCurrentFiniteMarginal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.NonnegativeCurrentConditionalPMF.Part5
import Theorem.StatisticalMechanics.Code.FrontierB.NonnegativeCurrentFiniteMarginal
open MeasureTheory
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def nonnegativeComplementParityKernel
    (lambda : Sym2 V → ℝ) (H : Finset (Sym2 V))
    (S : Finset G.edgeFinset)
    (b : {e : G.edgeFinset // e ∉ S} → ℕ) : ℝ :=
  ∏ e, nonnegativeParityEdgeKernel
    (lambda e.1.1) (e.1.1 ∈ H) (b e)

end StatMech.FrontierB
