/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BernsteinGelfandEquivalence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.LieGroups.code.HCBimoduleProjectives.Part2
public import Lemma.Fin.All_Eq.of.All_Eq.All_Eq_RightAction.All_Eq_RightAction.All_Any_Eq_Sum_RightAction
public import Lemma.Int.IsInQPlus0
public import Lemma.Int.WeightLE.of.BruhatLE
public import Lemma.Int.Level1.ne.Top
public import Lemma.Int.FGUeaIotaRange
public import Def.v1.Atlas.LieGroups.code.CategoryO.Part3
public import Def.v1.Atlas.LieGroups.code.CategoryOII.Part3
public import Def.v1.Atlas.LieGroups.code.JantzenFiltration.Part2
public import Def.v1.Atlas.LieGroups.code.DufloJoseph.Part8
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Analysis.Complex.Basic
public import Def.v1.Atlas.LieGroups.code.BernsteinGelfandEquivalence.Part6


public noncomputable section

open TensorProduct

universe u_R u_g u_mod

attribute [instance] LieModuleObj.instAddCommGroup LieModuleObj.instModule
  LieModuleObj.instLieRingModule LieModuleObj.instLieModule

variable {R : Type u_R} [CommRing R]

variable {g : Type u_g} [LieRing g] [LieAlgebra R g]

structure RealizingRepData
    (theta : CenterCharacter R g)
    (M : LieBimodule.{u_R, u_g, u_mod} R g)
    (_hM : IsInHCThetaOne M theta) where
  G : Type*
  [instGroupG : Group G]
  [instTopG : TopologicalSpace G]
  [instTopGroupG : IsTopologicalGroup G]
  [instSCG : SimplyConnectedSpace G]
  K : Subgroup G
  [instCompactK : CompactSpace K]
  V : Type*
  [instNACGV : NormedAddCommGroup V]
  [instIPSV : InnerProductSpace ℂ V]
  [instCompleteV : CompleteSpace V]
  [instModRV : Module R V]
  [instLieRingModuleGV : LieRingModule g V]
  [instLieModuleGV : LieModule R g V]
  π : Representation R G V
  admissible : IsAdmissibleRepresentation π K
  kFinBimod : LieBimodule.{u_R, u_g, u_mod} R g
  kFinInHCTheta : IsInHCThetaOne kFinBimod theta
  embedding : kFinBimod.carrier →ₗ[R] V
  embedding_injective : Function.Injective embedding
  embedding_lie_compat : ∀ (x : g) (w : kFinBimod.carrier),
    embedding (kFinBimod.leftAction (UniversalEnvelopingAlgebra.ι R x) w) =
    instLieRingModuleGV.bracket x (embedding w)
  embedding_KFinite : ∀ w : kFinBimod.carrier, IsKFiniteVector π K (embedding w)
  isoForward : HCThetaOneHom kFinBimod M theta kFinInHCTheta _hM
  isoBackward : HCThetaOneHom M kFinBimod theta _hM kFinInHCTheta
  iso_left_inv : ∀ m : M.carrier,
    isoForward.toLinearMap (isoBackward.toLinearMap m) = m
  iso_right_inv : ∀ v : kFinBimod.carrier,
    isoBackward.toLinearMap (isoForward.toLinearMap v) = v

end
