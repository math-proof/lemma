/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/NonnegativeCurrentConditionalPMF.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.InhomogeneousCurrentConditionalPMF.Part5
import Theorem.StatisticalMechanics.Code.FrontierB.NonnegativeCurrentConditionalPMF.Part3
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness Ising


section Graph

open Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def nonnegativeParityCurrentKernel
    (lambda : Sym2 V → ℝ) (H : Finset (Sym2 V))
    (m : EdgeCurrent G) : ℝ :=
  ∏ e : G.edgeFinset,
    nonnegativeParityEdgeKernel (lambda e.1) (e.1 ∈ H) (m e)

end Graph
end StatMech.FrontierB
