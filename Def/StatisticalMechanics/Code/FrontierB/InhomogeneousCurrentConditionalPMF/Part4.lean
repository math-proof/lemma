/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousCurrentConditionalPMF.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.CurrentParityDetermination.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.InhomogeneousCurrentConditionalPMF.Part3
open MeasureTheory
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness


section Graph

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def inhomogeneousParityCurrentPMF
    (lambda : Sym2 V -> Real)
    (hlambda : forall e : G.edgeFinset, 0 < lambda e.1)
    (H : Finset (Sym2 V)) : PMF (EdgeCurrent G) :=
  PMF.normalize
    (fun m => ENNReal.ofReal
      (inhomogeneousParityCurrentKernel G lambda H m))
    (by
      rw [tsum_ofReal_inhomogeneousParityCurrentKernel G lambda hlambda H]
      exact one_ne_zero)
    (by
      rw [tsum_ofReal_inhomogeneousParityCurrentKernel G lambda hlambda H]
      exact ENNReal.one_ne_top)

end Graph
end StatMech.FrontierB
