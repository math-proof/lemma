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
import Def.v1.Atlas.LieGroups.code.BernsteinGelfandEquivalence.Part2


noncomputable section

open TensorProduct

universe u_R u_g u_mod

attribute [instance] LieModuleObj.instAddCommGroup LieModuleObj.instModule
  LieModuleObj.instLieRingModule LieModuleObj.instLieModule

variable {R : Type u_R} [CommRing R]

variable {g : Type u_g} [LieRing g] [LieAlgebra R g]

noncomputable instance VermaCarrier.instACG (D : TriangularDecomposition R g)
    (wt : D.𝔥 →ₗ[R] R) : AddCommGroup (VermaCarrier D wt) :=
  (verma_module_exists (R := R) (𝔤 := g) D wt).choose_spec.choose

noncomputable instance VermaCarrier.instMod (D : TriangularDecomposition R g)
    (wt : D.𝔥 →ₗ[R] R) : Module R (VermaCarrier D wt) :=
  (verma_module_exists (R := R) (𝔤 := g) D wt).choose_spec.choose_spec.choose

noncomputable instance VermaCarrier.instLRM (D : TriangularDecomposition R g)
    (wt : D.𝔥 →ₗ[R] R) : LieRingModule g (VermaCarrier D wt) :=
  (verma_module_exists (R := R) (𝔤 := g) D wt).choose_spec.choose_spec.choose_spec.choose

noncomputable instance VermaCarrier.instLM (D : TriangularDecomposition R g)
    (wt : D.𝔥 →ₗ[R] R) : LieModule R g (VermaCarrier D wt) :=
  (verma_module_exists (R := R) (𝔤 := g) D wt).choose_spec.choose_spec.choose_spec.choose_spec.choose

end
