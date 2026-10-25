/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteBoundarySourceLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FiniteBoundarySwitching.Part2
import Def.StatisticalMechanics.Code.FrontierB.FiniteBoundarySourceLaw.Part2
open MeasureTheory
open scoped ENNReal BigOperators


namespace StatMech.FrontierB

open Finset Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem boundarySourceCurrentPMF_apply
    (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    (interior internalSources : Finset V)
    (hpos : 0 < boundarySourceCurrentSum G beta J interior internalSources)
    (m : EdgeCurrent G) :
    boundarySourceCurrentPMF G beta J hbeta hJ interior internalSources hpos m =
      boundarySourceCurrentRawMass G beta J interior internalSources m *
        (ENNReal.ofReal
          (boundarySourceCurrentSum G beta J interior internalSources))⁻¹ := by
  rw [boundarySourceCurrentPMF, PMF.normalize_apply,
    tsum_boundarySourceCurrentRawMass
      G beta J hbeta hJ interior internalSources]


end StatMech.FrontierB
