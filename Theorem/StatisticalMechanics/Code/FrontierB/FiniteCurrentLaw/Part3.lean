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
import Def.StatisticalMechanics.Code.FrontierB.FiniteCurrentLaw.Part3
open MeasureTheory
open scoped ENNReal BigOperators


namespace StatMech

namespace FrontierB

open Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem sourcelessCurrentMeasure_singleton (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e) (m : EdgeCurrent G) :
    (sourcelessCurrentMeasure G beta J hbeta hJ : Measure (EdgeCurrent G)) {m} =
      sourcelessCurrentPMF G beta J hbeta hJ m := by
  exact PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton m)


theorem sourcelessCurrentMeasure_sources (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e) :
    (sourcelessCurrentMeasure G beta J hbeta hJ : Measure (EdgeCurrent G))
      {m | sources G (ofEdgeFun G m) = ∅} = 1 := by
  change (sourcelessCurrentPMF G beta J hbeta hJ).toMeasure
    {m | sources G (ofEdgeFun G m) = ∅} = 1
  apply (PMF.toMeasure_apply_eq_one_iff _ (Set.to_countable _).measurableSet).2
  intro m hm
  by_contra hsrc
  have hmne : sourcelessCurrentPMF G beta J hbeta hJ m ≠ 0 :=
    (PMF.mem_support_iff _ _).1 hm
  have hzero : sourcelessCurrentPMF G beta J hbeta hJ m = 0 :=
    currentPMF_apply_eq_zero_of_sources_ne G beta J hbeta hJ ∅
      (Ising.acr_currentSum_empty_pos G beta J) m hsrc
  exact hmne hzero

end FrontierB
end StatMech
