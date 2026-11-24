module
public import Def.v1.Atlas.LieGroups.code.HCBimoduleProjectives.Part2
public import Theorem.Fin.All_Eq.of.All_Eq.All_Eq_RightAction.All_Eq_RightAction.All_Any_Eq_Sum_RightAction
public import Theorem.Int.IsInQPlus0
public import Theorem.Int.WeightLE.of.BruhatLE
public import Theorem.Int.Level1.ne.Top
public import Theorem.Int.FGUeaIotaRange
public import Def.v1.Atlas.LieGroups.code.CategoryO.Part3
public import Def.v1.Atlas.LieGroups.code.CategoryOII.Part3
public import Def.v1.Atlas.LieGroups.code.JantzenFiltration.Part2
public import Def.v1.Atlas.LieGroups.code.DufloJoseph.Part8
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Analysis.Complex.Basic
public import Def.v1.Atlas.LieGroups.code.BernsteinGelfandEquivalence.Part4


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BernsteinGelfandEquivalence.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

open TensorProduct

universe u_R u_g u_mod

attribute [instance] LieModuleObj.instAddCommGroup LieModuleObj.instModule
  LieModuleObj.instLieRingModule LieModuleObj.instLieModule

variable {R : Type u_R} [CommRing R]

variable {g : Type u_g} [LieRing g] [LieAlgebra R g]

abbrev HCThetaOneObj (R : Type u_R) [CommRing R] (g : Type u_g) [LieRing g] [LieAlgebra R g]
    (theta : CenterCharacter R g) :=
  { Y : LieBimodule.{u_R, u_g, u_mod} R g // IsInHCThetaOne Y theta }

end
