/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingTranslatedBoxClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.IsingPlusTIClose.Part5
import Theorem.StatisticalMechanics.Code.Ising.IsingCrossBoxCap.Part2
import Theorem.StatisticalMechanics.Code.Ising.IsingTranslatedBoxClose.Part2
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology BoundedContinuousFunction
open scoped BigOperators ENNReal StatMech

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.ConfigSpace

open StatMech.FK

variable {d : ℕ}


def itb_OffCentreDomination (β h : ℝ) (g : Multiplicative (Site d)) : Prop :=
  ∀ T : Finset (Site d), ∃ c : ℕ, ∀ m : ℕ,
    (plusMeasure d (m + c) β h : Measure (ConfigSpace (Site d))).real
        (fmu_multiOpen (E := Site d) T)
      ≤ (plusMeasure d m β h : Measure (ConfigSpace (Site d))).real
          (fmu_multiOpen (E := Site d) (T.image (fun x => g⁻¹ • x)))
    ∧ (plusMeasure d m β h : Measure (ConfigSpace (Site d))).real
          (fmu_multiOpen (E := Site d) (T.image (fun x => g⁻¹ • x)))
      ≤ (plusMeasure d (m - c) β h : Measure (ConfigSpace (Site d))).real
          (fmu_multiOpen (E := Site d) T)


end Ising
end StatMech
