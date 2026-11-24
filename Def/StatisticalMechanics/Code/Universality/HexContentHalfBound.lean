module
public import Theorem.StatisticalMechanics.Code.Universality.HexContentChoiceBound
public import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWContent.Part12
public import Theorem.StatisticalMechanics.Code.Universality.HexSurgerySeams.Part5
public import Theorem.StatisticalMechanics.Code.Universality.HexContentHalfBound


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexContentHalfBound.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open scoped BigOperators

noncomputable section

def hchb_find (s : HexHWContentHalf) (T : ℕ) : Option HexBridge :=
  s.1.find? (fun b => decide (b.width = T))

end
end StatMech.Universality
