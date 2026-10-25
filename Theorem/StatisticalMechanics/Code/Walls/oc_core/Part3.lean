/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.RevealmentCrossBox.Part7
import Theorem.StatisticalMechanics.Code.OSSS.SharpnessFK
import Theorem.StatisticalMechanics.Code.Walls.oc_boxcrossingscalesum
import Theorem.StatisticalMechanics.Code.Walls.oc_boxobjects.Part2
import Def.StatisticalMechanics.Code.Walls.oc_core.Part3
open scoped BigOperators
open Finset

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace StatMech

namespace Walls

open StatMech.OSSS

open StatMech.OSSS.DecisionTree

open StatMech.OSSS.Revealment

open StatMech.OSSS.RevealmentConstruction

open StatMech.Lattice

open scoped Classical

variable {E : Type*} [Fintype E] [DecidableEq E]


section Residue

variable {d : ℕ}


theorem oc_correlated_covLowerBound_of_bridge {ν : E → Bool → ℝ}
    (hν : IsProbWeight ν) {A : Set (ConfigSpace E)} (hA : IsIncreasing A)
    {κ : Type*} [Fintype κ] [Nonempty κ]
    (T : κ → DecisionTree E) (hT : ∀ k, (T k).evalR = A.indicator (fun _ => (1 : ℝ)))
    (R : κ → E → ℝ) (hreach : ∀ k e, reveal ν (T k) e ≤ R k e)
    (c₀ : ℝ) (hc₀nn : 0 ≤ c₀) (hc₀ : ∀ e, c₀ ≤ ν e true * ν e false)
    (D : ℝ) (hDnn : 0 ≤ D) (hsum : ∀ e, (∑ k, R k e) ≤ D)
    (θμ covCorr : ℝ)
    (hbridge : oc_CodingCovBridge (ν := ν) (A.indicator (fun _ => (1 : ℝ))) θμ covCorr) :
    (Fintype.card κ : ℝ) * c₀ * (θμ * (1 - θμ)) ≤ D * covCorr := by
  obtain ⟨hcov, hmean⟩ := hbridge
  rw [hmean, hcov]
  exact oc_familyAveraged_covLowerBound hν hA T hT R hreach c₀ hc₀nn hc₀ D hDnn hsum


theorem oc_codingCovBridge_refl {ν : E → Bool → ℝ} (f : ConfigSpace E → ℝ) :
    oc_CodingCovBridge (ν := ν) f (expect ν f) (∑ e, cov ν (CovLowerBound.coordI e) f) :=
  ⟨rfl, rfl⟩

end Residue
end Walls
end StatMech
