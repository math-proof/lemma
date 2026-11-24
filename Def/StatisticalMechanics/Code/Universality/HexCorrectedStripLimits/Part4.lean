module
public import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripAssembly.Part14
public import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripLimits.Part4


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripLimits.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

noncomputable def hexCSTopFinsetHeight
    {T : ℕ} {hT : 0 < T}
    (s : Finset {ts : List ℤ // HexCSTopWalkAtWidth T hT ts}) : ℕ :=
  s.sup hexCSTopWalkHeight


end
end StatMech.Universality
