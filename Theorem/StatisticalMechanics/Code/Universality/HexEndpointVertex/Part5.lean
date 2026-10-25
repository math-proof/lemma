/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointWalk.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexCyclicVertexPartition.Part9
import Theorem.StatisticalMechanics.Code.Universality.HexReturnUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexStripBandClose.Part7
import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part18
import Def.StatisticalMechanics.Code.Universality.HexEndpointVertex.Part5


namespace StatMech.Universality

open Complex Function HexWalk

open scoped BigOperators

noncomputable section

namespace HexFiniteRegion

variable (R : HexFiniteRegion)


@[simp] theorem mem_endpointCombinedSupportFinset
    (a : ℂ) (h0 : ℤ) (v du : ℂ) (ts : List ℤ) :
    ts ∈ R.endpointCombinedSupportFinset a h0 v du ↔
      endpointCombinedSummand R.inRegion a h0 v du ts ≠ 0 := by
  exact Set.Finite.mem_toFinset _

theorem endpointCombined_summable (a : ℂ) (h0 : ℤ) (v du : ℂ) :
    Summable (endpointCombinedSummand R.inRegion a h0 v du) := by
  apply summable_of_ne_finset_zero
    (s := R.endpointCombinedSupportFinset a h0 v du)
  intro ts hts
  by_contra hne
  exact hts ((R.mem_endpointCombinedSupportFinset a h0 v du ts).2 hne)


end HexFiniteRegion
end
end StatMech.Universality
