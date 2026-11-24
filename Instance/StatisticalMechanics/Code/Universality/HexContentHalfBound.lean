module
public import Theorem.StatisticalMechanics.Code.Universality.HexContentChoiceBound
public import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWContent.Part12
public import Theorem.StatisticalMechanics.Code.Universality.HexSurgerySeams.Part5


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

instance : Std.Irrefl
    (fun b c : HexBridge => b.width > c.width) where
  irrefl b := lt_irrefl b.width

instance : Std.Antisymm
    (fun b c : HexBridge => b.width > c.width) where
  antisymm _ _ hab hba := (lt_asymm hab hba).elim


end
end StatMech.Universality
