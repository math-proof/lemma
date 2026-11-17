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
public import Theorem.v1.Atlas.LieGroups.code.SL2Basics.Part2

@[expose] public section

attribute [local instance 100] LieRing.ofAssociativeRing

-- Mathlib keeps LieRing.ofAssociativeRing as a local instance only


noncomputable section

instance sl2C_finiteDimensional : FiniteDimensional ℂ sl2C := by
  have := finrank_sl2C
  exact Module.finite_of_finrank_pos (by omega)

instance sl2R_finiteDimensional : FiniteDimensional ℝ sl2R := by
  have := finrank_sl2R
  exact Module.finite_of_finrank_pos (by omega)

instance sl2C_free : Module.Free ℂ sl2C := Module.Free.of_divisionRing ..

instance sl2R_free : Module.Free ℝ sl2R := Module.Free.of_divisionRing ..

end
