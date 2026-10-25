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
import Def.v1.Atlas.LieGroups.code.SL2Basics.Part3
attribute [local instance 100] LieRing.ofAssociativeRing

-- Mathlib keeps LieRing.ofAssociativeRing as a local instance only


noncomputable section

theorem basisH_C_ne_zero : basisH_C ≠ 0 := by
  intro h
  have : basisH_C 0 0 = (0 : M2C) 0 0 := congr_fun (congr_fun h 0) 0
  simp [basisH_C] at this

theorem sl2H_ne_zero : sl2H ≠ 0 := by
  intro h
  have : sl2H.val = 0 := congr_arg Subtype.val h
  exact basisH_C_ne_zero this

theorem sl2_lie_EF : ⁅sl2E, sl2F⁆ = sl2H := by
  apply Subtype.ext
  show ⁅basisE_C, basisF_C⁆ = basisH_C
  exact lie_E_F_C

theorem sl2_lie_HE : ⁅sl2H, sl2E⁆ = 2 • sl2E := by
  apply Subtype.ext
  show ⁅basisH_C, basisE_C⁆ = 2 • basisE_C
  exact lie_H_E_C

theorem sl2_lie_HF : ⁅sl2H, sl2F⁆ = -(2 • sl2F) := by
  apply Subtype.ext
  show ⁅basisH_C, basisF_C⁆ = -(2 • basisF_C)
  rw [lie_H_F_C]; simp

theorem sl2_isSl2Triple : IsSl2Triple sl2H sl2E sl2F where
  h_ne_zero := sl2H_ne_zero
  lie_e_f := sl2_lie_EF
  lie_h_e_nsmul := sl2_lie_HE
  lie_h_f_nsmul := sl2_lie_HF

end
