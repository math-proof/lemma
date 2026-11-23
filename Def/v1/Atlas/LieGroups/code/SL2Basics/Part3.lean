/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Basics.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.Lie.Sl2
public import Mathlib.Algebra.Lie.Abelian
public import Theorem.v1.Atlas.LieGroups.code.SL2Basics.Part3

@[expose] public section

attribute [local instance 100] LieRing.ofAssociativeRing

-- Mathlib keeps LieRing.ofAssociativeRing as a local instance only


noncomputable section

def sl2H : ↥sl2C := ⟨basisH_C, basisH_C_mem_sl2C⟩

def sl2E : ↥sl2C := ⟨basisE_C, basisE_C_mem_sl2C⟩

def sl2F : ↥sl2C := ⟨basisF_C, basisF_C_mem_sl2C⟩

end
