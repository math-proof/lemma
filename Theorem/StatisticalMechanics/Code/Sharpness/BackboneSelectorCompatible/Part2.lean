/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSelectorCompatible.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneP2Quantitative
import Theorem.StatisticalMechanics.Code.Ising.CorrelationRatio
import Def.StatisticalMechanics.Code.Sharpness.BackboneSelectorCompatible.Part2
open SimpleGraph Finset

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]


theorem shb_pathMapLe_injective {H G : SimpleGraph V} (hHG : H ≤ G)
    {x y : V} : Function.Injective (shb_pathMapLe hHG : H.Path x y → G.Path x y) := by
  intro p q hpq
  apply Subtype.ext
  apply SimpleGraph.Walk.support_injective
  have hs := congrArg (fun r : G.Path x y => r.1.support) hpq
  simpa only [shb_pathMapLe, SimpleGraph.Walk.support_mapLe_eq_support] using hs


end StatMech.Sharpness
