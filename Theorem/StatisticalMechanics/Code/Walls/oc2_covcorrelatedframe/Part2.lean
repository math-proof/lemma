/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_covcorrelatedframe.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.MonotonicOSSS.Part3
import Theorem.StatisticalMechanics.Code.Walls.oc_core.Part3
import Def.StatisticalMechanics.Code.Walls.oc2_covcorrelatedframe.Part2
open scoped BigOperators
open Finset

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace StatMech

namespace Walls

open StatMech.OSSS

open StatMech.OSSS.MonotonicMeasure

open StatMech.OSSS.MonotonicFK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


lemma oc2_covCorrSum_eq_fkCovSum (p q : ℝ) (f : ConfigSpace (Sym2 V) → ℝ) :
    oc2_covCorrSum G p q f
      = ∑ e ∈ G.edgeFinset, FK.fkCov G p q f (FK.coord e) := by
  unfold oc2_covCorrSum
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [oc2_covCorr_eq_fkCov, oc2_coordRead_eq_coord]


lemma oc2_thetaCorr_eq_fkProbOf (p q : ℝ) (A : Set (ConfigSpace (Sym2 V))) :
    oc2_thetaCorr G p q (A.indicator (fun _ => (1 : ℝ)))
      = FK.fkProbOf G p q A := by
  unfold oc2_thetaCorr FK.fkProbOf
  exact oc2_meanCorr_eq_fkMean G p q _


lemma oc2_var_indicator_ccf (p q : ℝ) (A : Set (ConfigSpace (Sym2 V))) :
    oc2_covCorr G p q (A.indicator (fun _ => (1 : ℝ))) (A.indicator (fun _ => (1 : ℝ)))
      = FK.fkProbOf G p q A * (1 - FK.fkProbOf G p q A) := by
  rw [show oc2_covCorr G p q (A.indicator (fun _ => (1 : ℝ))) (A.indicator (fun _ => (1 : ℝ)))
        = genVar (fkMass G p q) (A.indicator (fun _ => (1 : ℝ))) from rfl]
  exact fkVar_indicator G p q A


variable {E : Type*} [Fintype E] [DecidableEq E]


theorem oc2_covCorrFrame_hits_bridge {ν : E → Bool → ℝ}
    (f : ConfigSpace E → ℝ) (θμ covCorr : ℝ) :
    oc_CodingCovBridge (ν := ν) f θμ covCorr
      ↔ (covCorr = ∑ e, cov ν (CovLowerBound.coordI e) f ∧ θμ = expect ν f) :=
  Iff.rfl


theorem oc2_covCorrFrame_codingFixedPoint {ν : E → Bool → ℝ} (f : ConfigSpace E → ℝ) :
    oc_CodingCovBridge (ν := ν) f (expect ν f) (∑ e, cov ν (CovLowerBound.coordI e) f) :=
  ⟨rfl, rfl⟩


theorem oc2_covCorrFrame_pinned {ν : E → Bool → ℝ}
    (f : ConfigSpace E → ℝ) (θμ covCorr : ℝ)
    (hbridge : oc_CodingCovBridge (ν := ν) f θμ covCorr) :
    covCorr = ∑ e, cov ν (CovLowerBound.coordI e) f ∧ θμ = expect ν f :=
  hbridge


theorem oc2_correlated_covLowerBound_frame
    {ν : Sym2 V → Bool → ℝ} (hν : IsProbWeight ν)
    {A : Set (ConfigSpace (Sym2 V))} (hA : IsIncreasing A)
    {κ : Type*} [Fintype κ] [Nonempty κ]
    (T : κ → DecisionTree (Sym2 V))
    (hT : ∀ k, (T k).evalR = A.indicator (fun _ => (1 : ℝ)))
    (R : κ → Sym2 V → ℝ) (hreach : ∀ k e, reveal ν (T k) e ≤ R k e)
    (c₀ : ℝ) (hc₀nn : 0 ≤ c₀) (hc₀ : ∀ e, c₀ ≤ ν e true * ν e false)
    (D : ℝ) (hDnn : 0 ≤ D) (hsum : ∀ e, (∑ k, R k e) ≤ D)
    (p qf : ℝ)
    (hbridge : oc_CodingCovBridge (ν := ν) (A.indicator (fun _ => (1 : ℝ)))
      (oc2_thetaCorr G p qf (A.indicator (fun _ => (1 : ℝ))))
      (oc2_covCorrSum G p qf (A.indicator (fun _ => (1 : ℝ))))) :
    (Fintype.card κ : ℝ) * c₀
        * (oc2_thetaCorr G p qf (A.indicator (fun _ => (1 : ℝ)))
            * (1 - oc2_thetaCorr G p qf (A.indicator (fun _ => (1 : ℝ)))))
      ≤ D * oc2_covCorrSum G p qf (A.indicator (fun _ => (1 : ℝ))) :=
  oc_correlated_covLowerBound_of_bridge (ν := ν) hν hA T hT R hreach c₀ hc₀nn hc₀ D hDnn hsum
    _ _ hbridge

end Walls
end StatMech
