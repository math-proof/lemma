/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BernsteinGelfandEquivalence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.HCBimoduleProjectives.Part2
import Lemma.Fin.All_Eq.of.All_Eq.All_Eq_RightAction.All_Eq_RightAction.All_Any_Eq_Sum_RightAction
import Lemma.Int.IsInQPlus0
import Lemma.Int.WeightLE.of.BruhatLE
import Lemma.Int.Level1.ne.Top
import Lemma.Int.FGUeaIotaRange
import Def.v1.Atlas.LieGroups.code.CategoryO.Part3
import Def.v1.Atlas.LieGroups.code.CategoryOII.Part3
import Def.v1.Atlas.LieGroups.code.JantzenFiltration.Part2
import Def.v1.Atlas.LieGroups.code.DufloJoseph.Part8
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.RepresentationTheory.Basic
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Analysis.Complex.Basic
import Def.v1.Atlas.LieGroups.code.BernsteinGelfandEquivalence.Part5


noncomputable section

open TensorProduct

universe u_R u_g u_mod

attribute [instance] LieModuleObj.instAddCommGroup LieModuleObj.instModule
  LieModuleObj.instLieRingModule LieModuleObj.instLieModule

variable {R : Type u_R} [CommRing R]

variable {g : Type u_g} [LieRing g] [LieAlgebra R g]

noncomputable instance LieModuleMor_ker_lieRingModule
    {X Y : LieModuleObj.{u_R, u_g, u_mod} R g}
    (f : LieModuleMor R g X Y) : LieRingModule g f.toLinearMap.ker where
  bracket x m := ⟨⁅x, m.1⁆, by
    simp [LinearMap.mem_ker]; rw [f.lie_compat, m.2, lie_zero]⟩
  add_lie x y m := Subtype.ext (add_lie x y m.1)
  lie_add x m n := Subtype.ext (lie_add x m.1 n.1)
  leibniz_lie x y m := Subtype.ext (leibniz_lie x y m.1)

noncomputable instance LieModuleMor_ker_lieModule
    {X Y : LieModuleObj.{u_R, u_g, u_mod} R g}
    (f : LieModuleMor R g X Y) : LieModule R g f.toLinearMap.ker where
  smul_lie r x m := by
    apply Subtype.ext; show ⁅r • x, m.1⁆ = r • ⁅x, m.1⁆; exact smul_lie r x m.1
  lie_smul r x m := by
    apply Subtype.ext; show ⁅x, r • m.1⁆ = r • ⁅x, m.1⁆; exact lie_smul r x m.1

end
