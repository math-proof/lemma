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
import Theorem.v1.Atlas.LieGroups.code.SL2Basics.Part2
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
