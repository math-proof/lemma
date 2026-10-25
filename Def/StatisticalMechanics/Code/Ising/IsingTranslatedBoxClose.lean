/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingTranslatedBoxClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.IsingPlusTIClose.Part5
import Theorem.StatisticalMechanics.Code.Ising.IsingCrossBoxCap.Part2
import Theorem.StatisticalMechanics.Code.Ising.IsingTranslatedBoxClose
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology BoundedContinuousFunction
open scoped BigOperators ENNReal StatMech

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.ConfigSpace

open StatMech.FK

variable {d : ℕ}


def itb_PlusMultiBoundaryDecay (β h : ℝ) (g : Multiplicative (Site d)) (φ : ℕ → ℕ) : Prop :=
  ∀ T : Finset (Site d),
    Tendsto (fun n =>
      ((plusMeasure d (φ n) β h : Measure (ConfigSpace (Site d))).real
          (fmu_multiOpen (E := Site d) T))
        - ((plusMeasure d (φ n) β h : Measure (ConfigSpace (Site d))).real
            (fmu_multiOpen (E := Site d) (T.image (fun x => g⁻¹ • x)))))
      atTop (𝓝 0)


end Ising
end StatMech
