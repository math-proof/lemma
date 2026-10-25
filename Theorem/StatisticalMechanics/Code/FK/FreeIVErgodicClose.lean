/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeIVErgodicClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.CrossBoxGeneralKeystone.Part3
import Theorem.StatisticalMechanics.Code.FK.FKTwoBoxDecoupling.Part2
import Theorem.StatisticalMechanics.Code.FK.FKWiredDomainMonotone.Part2
import Theorem.StatisticalMechanics.Code.FK.FKMixingUpperClose.Part5
open MeasureTheory Filter Topology Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedVariables false


namespace StatMech

namespace FK

open ConfigSpace

variable {d : ℕ}


theorem fie_freeIV_isErgodic_of_eq_wired {p : ℝ} (hd : 1 ≤ d) (hp : 0 < p) (hp1 : p < 1)
    (heq : (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d))))
      = (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d))))) :
    IsErgodic (G := Multiplicative (Site d))
      (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))) := by
  rw [heq]
  exact cbk_wiredIV_isErgodic hd hp hp1


end FK
end StatMech
