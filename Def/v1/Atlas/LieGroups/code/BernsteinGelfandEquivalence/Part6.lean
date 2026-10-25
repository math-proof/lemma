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
import Instance.v1.Atlas.LieGroups.code.BernsteinGelfandEquivalence.Part2


noncomputable section

open TensorProduct

universe u_R u_g u_mod

attribute [instance] LieModuleObj.instAddCommGroup LieModuleObj.instModule
  LieModuleObj.instLieRingModule LieModuleObj.instLieModule

variable {R : Type u_R} [CommRing R]

variable {g : Type u_g} [LieRing g] [LieAlgebra R g]

noncomputable def LieModuleMor_kerObj
    {X Y : LieModuleObj.{u_R, u_g, u_mod} R g}
    (f : LieModuleMor R g X Y) : LieModuleObj.{u_R, u_g, u_mod} R g where
  carrier := f.toLinearMap.ker

noncomputable def LieModuleMor_corestrToKer
    {A B C : LieModuleObj.{u_R, u_g, u_mod} R g}
    (q₁ : LieModuleMor R g A B) (q₀ : LieModuleMor R g B C)
    (hcomp : ∀ m : A.carrier, q₀.toLinearMap (q₁.toLinearMap m) = 0) :
    LieModuleMor R g A (LieModuleMor_kerObj q₀) where
  toLinearMap := q₁.toLinearMap.codRestrict q₀.toLinearMap.ker (fun m => by
    simp [LinearMap.mem_ker]; exact hcomp m)
  lie_compat x m := by
    apply Subtype.ext
    show q₁.toLinearMap ⁅x, m⁆ = ⁅x, q₁.toLinearMap m⁆
    exact q₁.lie_compat x m

def IsKFiniteVector
    {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module R V]
    (π : Representation R G V) (K : Subgroup G) (v : V) : Prop :=
  (Submodule.span R (Set.range (fun k : K => π k v))).FG

def IsAdmissibleRepresentation
    {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module R V]
    (π : Representation R G V) (K : Subgroup G) : Prop :=
  ∀ v : V, IsKFiniteVector π K v →
    ∃ (S : Submodule R V), Module.Finite R S ∧ v ∈ S ∧
      ∀ (k : K) (s : V), s ∈ S → π (k : G) s ∈ S

end
