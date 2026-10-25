/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteBoundarySourceLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FiniteBoundarySwitching.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.FiniteBoundarySourceLaw.Part2
open MeasureTheory
open scoped ENNReal BigOperators


namespace StatMech.FrontierB

open Finset Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def boundarySourceCurrentPairPMF
    (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    (interior internalSources exactSecondSources : Finset V)
    (hfirst : 0 < boundarySourceCurrentSum
      G beta J interior internalSources)
    (hsecond : 0 < currentSum G beta J exactSecondSources) :
    PMF (EdgeCurrent G × EdgeCurrent G) :=
  (boundarySourceCurrentPMF G beta J hbeta hJ
      interior internalSources hfirst).bind fun m =>
    (currentPMF G beta J hbeta hJ exactSecondSources hsecond).map
      (Prod.mk m)

end StatMech.FrontierB
