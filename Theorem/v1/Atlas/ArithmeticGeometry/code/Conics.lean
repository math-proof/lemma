/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Conics.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.HasseMinkowski
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.HasseMinkowski
import Mathlib
import Def.v1.Atlas.ArithmeticGeometry.code.Conics
variable [Invertible (2 : K)]


section Theorem23

variable {K : Type*} [Field K]

/-- Quadratic homogeneity: scaling the input $(U, V)$ by $t$ scales the stereographic forward map by $t^2$ (so it descends to projective space). -/
theorem stereoForward_smul (a b x₀ y₀ z₀ t U V : K) (i : Fin 3) :
    stereoForward a b x₀ y₀ z₀ (t * U) (t * V) i =
    t ^ 2 * stereoForward a b x₀ y₀ z₀ U V i := by
  fin_cases i <;> simp only [stereoForward] <;> ring


end Theorem23
