/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousCurrentConditionalPMF.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.CurrentParityDetermination.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.InhomogeneousCurrentConditionalPMF.Part2
open MeasureTheory
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness


section Graph

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def inhomogeneousParityCurrentKernel
    (lambda : Sym2 V -> Real) (H : Finset (Sym2 V))
    (m : EdgeCurrent G) : Real :=
  ∏ e : G.edgeFinset, parityEdgeKernel (lambda e.1) (e.1 ∈ H) (m e)

end Graph
end StatMech.FrontierB
