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
import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentLaw.Part2
open MeasureTheory
open scoped ENNReal BigOperators


namespace StatMech

namespace FrontierB

open Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def sourcelessCurrentPMF (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e) : PMF (EdgeCurrent G) :=
  currentPMF G beta J hbeta hJ ∅ (Ising.acr_currentSum_empty_pos G beta J)


noncomputable def sourcelessCurrentMeasure (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e) :
    ProbabilityMeasure (EdgeCurrent G) :=
  ⟨(sourcelessCurrentPMF G beta J hbeta hJ).toMeasure, inferInstance⟩


end FrontierB
end StatMech
