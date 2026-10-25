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
import Def.v1.Atlas.LieGroups.code.BernsteinGelfandEquivalence.Part6


noncomputable section

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
