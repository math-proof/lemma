/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Theorem.StatisticalMechanics.Code.Ising.CorrelationRatio
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentLaw
open MeasureTheory
open scoped ENNReal BigOperators


namespace StatMech

namespace FrontierB

open Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def currentPMF (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e) (A : Finset V)
    (hA : 0 < currentSum G beta J A) : PMF (EdgeCurrent G) :=
  PMF.normalize (currentRawMass G beta J A)
    (by
      rw [tsum_currentRawMass G beta J hbeta hJ A]
      exact (ENNReal.ofReal_pos.mpr hA).ne')
    (by
      rw [tsum_currentRawMass G beta J hbeta hJ A]
      exact ENNReal.ofReal_ne_top)


end FrontierB
end StatMech
