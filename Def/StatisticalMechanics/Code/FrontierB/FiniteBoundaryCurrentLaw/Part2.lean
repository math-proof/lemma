/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteBoundaryCurrentLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentTightness
import Theorem.StatisticalMechanics.Code.FrontierB.FiniteBoundaryCurrentLaw
open MeasureTheory
open scoped ENNReal BigOperators


namespace StatMech.FrontierB

open Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def boundaryCurrentPMF (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e) (interior : Finset V) :
    PMF (EdgeCurrent G) :=
  PMF.normalize (boundaryCurrentRawMass G beta J interior)
    (by
      rw [tsum_boundaryCurrentRawMass G beta J hbeta hJ interior]
      exact (ENNReal.ofReal_pos.mpr
        (lt_of_lt_of_le Real.zero_lt_one
          (one_le_boundaryCurrentSum G beta J hbeta hJ interior))).ne')
    (by
      rw [tsum_boundaryCurrentRawMass G beta J hbeta hJ interior]
      exact ENNReal.ofReal_ne_top)


end StatMech.FrontierB
