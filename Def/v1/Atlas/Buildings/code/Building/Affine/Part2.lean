/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Affine.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Structure.v1.Atlas.Buildings.code.Building.Basic.Part2
public import Structure.v1.Atlas.Buildings.code.Building.ApartmentsCoxeter
public import Structure.v1.Atlas.Buildings.code.BNPair.Basic.Part2
public import Mathlib.GroupTheory.Coxeter.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Structure.v1.Atlas.Buildings.code.Building.Affine

@[expose] public section

set_option linter.unusedSectionVars false

open ChamberComplex

variable {V : Type*} [DecidableEq V]


/-- The underlying subgroup of an Iwahori datum: the distinguished subgroup $B$
of the BN-pair. -/
def IwahoriSubgroup.toSubgroup {G : Type*} [Group G] {B_idx : Type*}
    {M : CoxeterMatrix B_idx} (I : IwahoriSubgroup G M) : Subgroup G :=
  I.bnpair.B

