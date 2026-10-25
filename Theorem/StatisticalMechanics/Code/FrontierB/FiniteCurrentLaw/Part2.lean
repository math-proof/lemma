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
import Def.StatisticalMechanics.Code.FrontierB.FiniteCurrentLaw.Part2
open MeasureTheory
open scoped ENNReal BigOperators


namespace StatMech

namespace FrontierB

open Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem currentPMF_apply (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e) (A : Finset V)
    (hA : 0 < currentSum G beta J A) (m : EdgeCurrent G) :
    currentPMF G beta J hbeta hJ A hA m =
      currentRawMass G beta J A m *
        (ENNReal.ofReal (currentSum G beta J A))⁻¹ := by
  rw [currentPMF, PMF.normalize_apply, tsum_currentRawMass G beta J hbeta hJ A]


theorem currentPMF_apply_eq_zero_of_sources_ne (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e) (A : Finset V)
    (hA : 0 < currentSum G beta J A) (m : EdgeCurrent G)
    (hm : sources G (ofEdgeFun G m) ≠ A) :
    currentPMF G beta J hbeta hJ A hA m = 0 := by
  rw [currentPMF_apply]
  simp [currentRawMass, hm]


end FrontierB
end StatMech
