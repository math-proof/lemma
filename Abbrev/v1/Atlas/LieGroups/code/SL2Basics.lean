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
attribute [local instance 100] LieRing.ofAssociativeRing

-- Mathlib keeps LieRing.ofAssociativeRing as a local instance only


noncomputable section

abbrev M2 := Matrix (Fin 2) (Fin 2) ℝ

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

abbrev SL2R := Matrix.SpecialLinearGroup (Fin 2) ℝ

end
