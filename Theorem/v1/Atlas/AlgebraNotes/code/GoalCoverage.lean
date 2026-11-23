/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/GoalCoverage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Theorem.Nat.IsPGroupG.is.CardG.eq.Pow
public import Lemma.Fin.Any_EqToBilin'AndIsSymm.is.IsSymmToMatrix'
public import Theorem.Matrix.MulMulStar.eq.Diagonal.of.IsStarNormal
public import Theorem.ZMod.Any_Nonempty_ZModPow
public import Def.v1.Atlas.AlgebraNotes.code.DiscreteGroups
public import Theorem.Matrix.MulMul_ConstVAdd.eq.ConstVAdd
public import Theorem.v1.Atlas.AlgebraNotes.code.SymmetryGroups

public section

noncomputable section

open MulAction Subgroup LinearMap Module Matrix

end
