/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCodingLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.GrandCouplingAssembly.Part6
import Def.StatisticalMechanics.Code.OSSS.AdaptiveCodingLaw.Part2
open scoped BigOperators
open MeasureTheory

set_option linter.style.longLine false
set_option linter.style.show false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false


namespace StatMech

namespace OSSS

namespace AdaptiveCodingLaw

open Coding GrandCoupling GrandCouplingAssembly Monotonic

variable {E : Type*} [Fintype E] [DecidableEq E]


lemma measurableSet_adaptiveFibre (μ : ConfigSpace E → ℝ) {n : ℕ}
    (σ : ConfigSpace E → (Fin n ≃ E)) (x : ConfigSpace E) :
    MeasurableSet (adaptiveFibre μ σ x) := by
  exact (measurable_codeMap μ (σ x)) (measurableSet_singleton x)


lemma vcube_adaptiveFibre (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : ConfigSpace E → (Fin n ≃ E))
    (x : ConfigSpace E) :
    ((Vcube n) (adaptiveFibre μ σ x)).toReal = μ x := by
  exact vcube_fibre μ hpos hμ1 (σ x) x


theorem predictable_adaptive_fibres_full_measure (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1) {n : ℕ}
    (σ : ConfigSpace E → (Fin n ≃ E)) (hσ : PredictableOrder σ) :
    ((Vcube n) (⋃ x, adaptiveFibre μ σ x)).toReal = 1 := by
  have hdisj : ∀ x ∈ (Finset.univ : Finset (ConfigSpace E)),
      ∀ y ∈ (Finset.univ : Finset (ConfigSpace E)), x ≠ y →
        Disjoint (adaptiveFibre μ σ x) (adaptiveFibre μ σ y) := by
    intro x _ y _ hxy
    exact predictable_fibres_disjoint μ σ hσ hxy
  have hmeas : ∀ x ∈ (Finset.univ : Finset (ConfigSpace E)),
      MeasurableSet (adaptiveFibre μ σ x) := by
    intro x _
    exact measurableSet_adaptiveFibre μ σ x
  have hmeasure : (Vcube n) (⋃ x, adaptiveFibre μ σ x) =
      ∑ x : ConfigSpace E, (Vcube n) (adaptiveFibre μ σ x) := by
    rw [← measure_biUnion_finset hdisj hmeas]
    congr 1
    ext u
    simp
  rw [hmeasure, ENNReal.toReal_sum (fun x _ => measure_ne_top (Vcube n) _)]
  simp_rw [vcube_adaptiveFibre μ hpos hμ1 σ]
  exact hμ1


end AdaptiveCodingLaw
end OSSS
end StatMech
