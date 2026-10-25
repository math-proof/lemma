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
open MeasureTheory Set Filter Function
open scoped BigOperators ENNReal Topology


namespace StatMech

namespace FK

open ConfigSpace Lattice

variable {d : ℕ}


noncomputable def freeAxisTranslation (hd : 1 ≤ d) :
    Multiplicative (Site d) :=
  Multiplicative.ofAdd fun i => if i = ⟨0, hd⟩ then 1 else 0


noncomputable def freeAxisTranslationPower (hd : 1 ≤ d) (n : ℕ) :
    Multiplicative (Site d) :=
  Multiplicative.ofAdd fun i => if i = ⟨0, hd⟩ then (n : ℤ) else 0

end FK
end StatMech
