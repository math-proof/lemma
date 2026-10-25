/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentPairLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FiniteNormalizedSwitching
import Theorem.StatisticalMechanics.Code.Sharpness.DeltaBound.Part2
open MeasureTheory
open scoped ENNReal symmDiff


namespace StatMech.FrontierB

open Finset Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def sourceCurrentPairPMF
    (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    (A B : Finset V)
    (hA : 0 < currentSum G beta J A)
    (hB : 0 < currentSum G beta J B) :
    PMF (EdgeCurrent G × EdgeCurrent G) :=
  (currentPMF G beta J hbeta hJ A hA).bind fun m =>
    (currentPMF G beta J hbeta hJ B hB).map (Prod.mk m)


end StatMech.FrontierB
