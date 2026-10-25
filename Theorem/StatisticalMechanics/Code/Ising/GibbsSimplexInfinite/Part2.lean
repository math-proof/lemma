/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsSimplexInfinite.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GibbsSimplex.Part3
import Theorem.StatisticalMechanics.Code.Ising.GibbsExtreme
import Theorem.StatisticalMechanics.Code.Ising.GibbsChoquet.Part2
import Theorem.StatisticalMechanics.Code.Foundations.StochasticDomination
import Notation.StatisticalMechanics.Code.Ising.GibbsSimplexInfinite
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology
open scoped BigOperators ENNReal StatMech

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.Lattice

variable {d : ℕ}


@[refl] theorem StochasticallyDominatedClopen.refl {E : Type*}
    (μ : Measure (ConfigSpace E)) : μ ≼c μ := fun _ _ _ => le_refl _


theorem StochasticallyDominatedClopen.trans {E : Type*} {μ ν ρ : Measure (ConfigSpace E)}
    (h₁ : μ ≼c ν) (h₂ : ν ≼c ρ) : μ ≼c ρ :=
  fun A hA hAu => (h₁ A hA hAu).trans (h₂ A hA hAu)


theorem StochasticallyDominated.toClopen {E : Type*} [Countable E]
    {μ ν : Measure (ConfigSpace E)} (h : μ ≼ ν) : μ ≼c ν :=
  fun A hA hAu => h A hA.2.measurableSet hAu


theorem gsi_infinite_volume_sandwich (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (μ : Measure (ConfigSpace (Site d))) [IsProbabilityMeasure μ]
    (hμ : IsDLRState d β h μ) :
    (minusState d β h : Measure (ConfigSpace (Site d))) ≼c μ
    ∧ μ ≼c (plusState d β h : Measure (ConfigSpace (Site d))) := by
  refine ⟨fun A hAcl hAu => ?_, fun A hAcl hAu => ?_⟩
  · exact gsi_minusState_le_dlr_open β h hβ hh μ hμ hAcl.2 hAu
  · exact gsi_dlr_le_plusState_closed β h hβ hh μ hμ hAcl.1 hAu


end Ising
end StatMech
