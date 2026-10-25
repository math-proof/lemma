/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreePairMixingFromTail.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FK.FreeTailTriviality
import Theorem.StatisticalMechanics.Code.FK.FKTwoBoxDecoupling.Part2
import Theorem.StatisticalMechanics.Code.Foundations.BirkhoffErgodic
import Theorem.StatisticalMechanics.Code.FK.FreePairMixingFromTail.Part2
open MeasureTheory Set Filter Function
open scoped BigOperators ENNReal Topology


namespace StatMech

namespace FK

open ConfigSpace Lattice

variable {d : ℕ}


noncomputable def freePairGap
    (hd : 1 ≤ d) (mu : Measure (ConfigSpace (Sym2 (Site d))))
    (T U : Finset (Sym2 (Site d))) (k : ℕ) : ℝ :=
  mu.real (fmu_multiOpen T ∩
      shift (freeAxisTranslationPower hd k) ⁻¹' fmu_multiOpen U) -
    mu.real (fmu_multiOpen T) * mu.real (fmu_multiOpen U)

end FK
end StatMech
