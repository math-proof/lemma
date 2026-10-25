/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/MonotonicOSSS.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.Coding.Part6
import Theorem.StatisticalMechanics.Code.OSSS.CovLowerBound
import Theorem.StatisticalMechanics.Code.FK.FKG
import Theorem.StatisticalMechanics.Code.FK.RussoDerivative.Part5
import Def.StatisticalMechanics.Code.OSSS.MonotonicOSSS.Part3
open scoped BigOperators
open Finset MeasureTheory Set

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace OSSS

namespace MonotonicFK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

open MonotonicMeasure


theorem monotonicOSSS_to_fkCov (p : ℝ)
    (A : Set (ConfigSpace (Sym2 V))) (N : ℕ) (c₀ D : ℝ)
    (hMonOSSS : MonotonicOSSSBound (fkMass G p 2) G.edgeFinset
      (A.indicator (fun _ => (1 : ℝ))) N c₀ D) :
    (N : ℝ) * c₀
        * (FK.fkProbOf G p 2 A * (1 - FK.fkProbOf G p 2 A))
      ≤ D * ∑ e ∈ G.edgeFinset,
          FK.fkCov G p 2 (A.indicator (fun _ => (1 : ℝ))) (FK.coord e) := by
  unfold MonotonicOSSSBound at hMonOSSS
  
  rw [fkVar_indicator G p 2 A] at hMonOSSS
  
  refine hMonOSSS.trans_eq ?_
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  
  rw [genCov_fkMass, genCoord_eq_coord]
  unfold FK.fkCov
  rw [show (fun ω => FK.coord e ω * A.indicator (fun _ => (1 : ℝ)) ω)
        = (fun ω => A.indicator (fun _ => (1 : ℝ)) ω * FK.coord e ω) from by funext ω; ring]
  ring

end MonotonicFK


namespace MonotonicMeasure

variable {E : Type*} [Fintype E] [DecidableEq E]

variable {ν : E → Bool → ℝ}

open StatMech.OSSS StatMech.OSSS.CovLowerBound


lemma genMean_weight (g : ConfigSpace E → ℝ) :
    genMean (weight ν) g = expect ν g := by
  unfold genMean expect
  exact Finset.sum_congr rfl (fun ω _ => by rw [mul_comm])


lemma genCov_weight (f g : ConfigSpace E → ℝ) :
    genCov (weight ν) f g = cov ν f g := by
  unfold genCov cov
  rw [genMean_weight, genMean_weight, genMean_weight]


lemma genVar_weight (g : ConfigSpace E → ℝ) :
    genVar (weight ν) g = var ν g := by
  unfold genVar var; rw [genCov_weight]


lemma genCoord_eq_coordI (e : E) : (genCoord e : ConfigSpace E → ℝ) = coordI e := by
  funext ω; unfold genCoord coordI; rfl


theorem monotonicOSSSBound_of_product {κ : Type*} [Fintype κ] [Nonempty κ]
    (hν : IsProbWeight ν) {A : Set (ConfigSpace E)} (hA : IsIncreasing A)
    {f : ConfigSpace E → ℝ} (hf : f = A.indicator (fun _ => (1 : ℝ)))
    (T : κ → DecisionTree E) (hT : ∀ k, (T k).evalR = f)
    (R : κ → E → ℝ) (hR : ∀ k e, reveal ν (T k) e ≤ R k e)
    (c₀ : ℝ) (hc₀nn : 0 ≤ c₀) (hc₀ : ∀ e, c₀ ≤ ν e true * ν e false)
    (D : ℝ) (hDnn : 0 ≤ D) (hD : ∀ e, (∑ k, R k e) ≤ D) :
    MonotonicOSSSBound (weight ν) Finset.univ f (Fintype.card κ) c₀ D := by
  unfold MonotonicOSSSBound
  rw [genVar_weight]
  have hmain := cov_lower_bound hν hA hf T hT R hR c₀ hc₀nn hc₀ D hDnn hD
  refine hmain.trans_eq ?_
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  rw [genCov_weight, genCoord_eq_coordI, cov_comm]

end MonotonicMeasure
end OSSS
end StatMech
