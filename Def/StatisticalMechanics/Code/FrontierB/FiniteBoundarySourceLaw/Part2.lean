/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteBoundarySourceLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FiniteBoundarySwitching.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.FiniteBoundarySourceLaw
open MeasureTheory
open scoped ENNReal BigOperators


namespace StatMech.FrontierB

open Finset Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def boundarySourceCurrentPMF
    (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    (interior internalSources : Finset V)
    (hpos : 0 < boundarySourceCurrentSum G beta J interior internalSources) :
    PMF (EdgeCurrent G) :=
  PMF.normalize
    (boundarySourceCurrentRawMass G beta J interior internalSources)
    (by
      rw [tsum_boundarySourceCurrentRawMass
        G beta J hbeta hJ interior internalSources]
      exact (ENNReal.ofReal_pos.mpr hpos).ne')
    (by
      rw [tsum_boundarySourceCurrentRawMass
        G beta J hbeta hJ interior internalSources]
      exact ENNReal.ofReal_ne_top)

end StatMech.FrontierB
