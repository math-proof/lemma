module
public import Theorem.StatisticalMechanics.Code.Universality.HexEndpointWalk.Part3
public import Theorem.StatisticalMechanics.Code.Universality.HexCyclicVertexPartition.Part9
public import Theorem.StatisticalMechanics.Code.Universality.HexReturnUniqueness.Part3
public import Theorem.StatisticalMechanics.Code.Universality.HexStripBandClose.Part7
public import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part18
public import Theorem.StatisticalMechanics.Code.Universality.HexEndpointVertex.Part4


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open Complex Function HexWalk

open scoped BigOperators

noncomputable section

namespace HexFiniteRegion

variable (R : HexFiniteRegion)


noncomputable def endpointCombinedSupportFinset
    (a : ℂ) (h0 : ℤ) (v du : ℂ) : Finset (List ℤ) :=
  (R.endpointCombined_support_finite a h0 v du).toFinset

end HexFiniteRegion
end
end StatMech.Universality
