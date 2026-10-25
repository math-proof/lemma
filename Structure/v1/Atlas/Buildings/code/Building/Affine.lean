/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Affine.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.Buildings.code.Building.Basic.Part2
import Lemma.Finset.Any_And_All_Eq.of.IsMaximal.In_Faces.In_Apartments
import Lemma.Finset.IsMaximalToSimplicialComplex.of.IsMaximal.In_Apartments
import Structure.v1.Atlas.Buildings.code.Building.ApartmentsCoxeter
import Structure.v1.Atlas.Buildings.code.BNPair.Basic.Part2
import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Def.v1.Atlas.Buildings.code.Building.Affine
set_option linter.unusedSectionVars false

open ChamberComplex

variable {V : Type*} [DecidableEq V]


/-- The Iwahori subgroup of a group $G$ from a BN-pair with indecomposable
affine Coxeter type: bundled data consisting of the BN-pair together with
the indecomposable affine hypotheses on its Coxeter matrix. -/
structure IwahoriSubgroup (G : Type*) [Group G] {B_idx : Type*}
    (M : CoxeterMatrix B_idx) where
  bnpair : BNPair G M
  indecomposable : M.IsIndecomposable
  affine : M.IsAffine

