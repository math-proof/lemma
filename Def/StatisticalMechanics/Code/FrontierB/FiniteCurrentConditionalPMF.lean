/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentConditionalPMF.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentConditional.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentConditionalPMF
open MeasureTheory
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def parityCurrentPMF (beta : ℝ) (hbeta : 0 < beta)
    (H : Finset (Sym2 V)) : PMF (EdgeCurrent G) :=
  PMF.normalize (fun m => ENNReal.ofReal (parityCurrentKernel G beta H m))
    (by rw [tsum_ofReal_parityCurrentKernel G beta hbeta H]; exact one_ne_zero)
    (by rw [tsum_ofReal_parityCurrentKernel G beta hbeta H]; exact ENNReal.one_ne_top)

end StatMech.FrontierB
