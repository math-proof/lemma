/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSelectorCompatible.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneP2Quantitative
import Theorem.StatisticalMechanics.Code.Ising.CorrelationRatio
import Def.StatisticalMechanics.Code.Sharpness.BackboneSelectorCompatible
open SimpleGraph Finset

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]


theorem shb_supportPathOrder_mapLe_iff
    {H G : SimpleGraph V} (hHG : H ≤ G) {x y : V}
    (p q : H.Path x y) :
    (p.1.mapLe hHG).support < (q.1.mapLe hHG).support ↔
      p.1.support < q.1.support := by
  simp only [SimpleGraph.Walk.support_mapLe_eq_support]


end StatMech.Sharpness
