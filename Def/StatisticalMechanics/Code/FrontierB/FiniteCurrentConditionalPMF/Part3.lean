/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentConditionalPMF.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentConditional.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentConditionalPMF.Part3
open MeasureTheory
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def finiteParityPMF {E : Type*} [DecidableEq E]
    (S : Finset E) (beta : ℝ) (hbeta : 0 < beta)
    (odd : ↑S → Bool) : PMF (↑S → ℕ) :=
  PMF.normalize (fun a => ENNReal.ofReal (finiteParityKernel S beta odd a))
    (by rw [tsum_ofReal_finiteParityKernel S beta hbeta odd]; exact one_ne_zero)
    (by rw [tsum_ofReal_finiteParityKernel S beta hbeta odd]; exact ENNReal.one_ne_top)

end StatMech.FrontierB
