/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Basics.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Lie.Sl2
import Mathlib.Algebra.Lie.Abelian
import Theorem.v1.Atlas.LieGroups.code.SL2Basics.Part3
attribute [local instance 100] LieRing.ofAssociativeRing

-- Mathlib keeps LieRing.ofAssociativeRing as a local instance only


noncomputable section

def sl2H : ↥sl2C := ⟨basisH_C, basisH_C_mem_sl2C⟩

def sl2E : ↥sl2C := ⟨basisE_C, basisE_C_mem_sl2C⟩

def sl2F : ↥sl2C := ⟨basisF_C, basisF_C_mem_sl2C⟩

end
