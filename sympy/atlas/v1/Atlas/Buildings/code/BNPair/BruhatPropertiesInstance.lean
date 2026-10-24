/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/BruhatPropertiesInstance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.BNPair.CellCoverProof
import Lemma.Nat.In_BruhatCell1.of.In_B
import Lemma.Nat.In_BruhatCell.of.In_BruhatCell
import Lemma.Nat.Simple.ne.One
import Lemma.Group.Atlas.v1.Buildings.code.BNPair.CellMulParabolicProof
import Lemma.Set.SetMul_SetMul
import Lemma.Set.BruhatCell.sub.SetG.of.In_BruhatCell.In_SetG.LeB
import Lemma.Nat.B.le.Closure_BruhatCell
import Lemma.Set.All_In_StandardParabolic
import Lemma.Nat.NonemptyBruhatCell
import sympy.atlas.v1.Atlas.Buildings.code.BNPair.CellInvProof
import sympy.atlas.v1.Atlas.Buildings.code.BNPair.CellDisjointProof
import sympy.atlas.v1.Atlas.Buildings.code.BNPair.CellMulParabolicProof
import sympy.atlas.v1.Atlas.Buildings.code.BNPair.CellMulFiniteProof
import Lemma.Real.EqSigma.of.Ne
import sympy.atlas.v1.Atlas.Buildings.code.BNPair.SubgroupOverBProof
import sympy.atlas.v1.Atlas.Buildings.code.BNPair.NormalizerParabolicProof
import sympy.atlas.v1.Atlas.Buildings.code.BNPair.ConjugatorProof
import sympy.atlas.v1.Atlas.Buildings.code.BNPair.ParabolicDefs

set_option linter.unusedSectionVars false

variable {G : Type*} [Group G] {B_idx : Type*} [DecidableEq B_idx] [Fintype B_idx]
  {M : CoxeterMatrix B_idx}

/-- Assemble the full `BruhatProperties` bundle (cell cover/disjointness/inversion/multiplication
within parabolics, conjugator targeting, finiteness) for a BN-pair from its axioms. -/
noncomputable def BNPair.BruhatProperties.fromAxioms
    (bp : BNPair G M) (ax : BNPairAxioms bp) : BNPair.BruhatProperties bp where
  cell_disjoint := CellDisjoint.cell_disjoint_from_bnpair bp ax
  cell_cover := CellCover.cell_cover_from_bnpair bp ax
  cell_inv := fun w g hg => BNPair.cell_inv_from_bnpair bp w g hg
  cell_mul_in_parabolic := CellMulParabolic.cell_mul_in_parabolic_from_bnpair bp ax
  parabolicW_injective := fun S₁ S₂ h =>
    M.toCoxeterSystem.parabolicSubgroup_injective S₁ S₂ h
  subgroup_over_B_eq_parabolic := SubgroupOverB.subgroup_over_B_eq_parabolic_from_bnpair bp ax
  normalizer_in_parabolic := NormalizerParabolic.normalizer_in_parabolic_from_bnpair bp ax
  conjugator_in_target := ConjugatorProof.conjugator_in_target_from_bnpair bp ax
  cell_mul_finite := CellMulFinite.cell_mul_finite_from_bnpair bp ax
