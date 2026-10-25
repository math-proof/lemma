/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/HeckeAlgebra/Generic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.GroupTheory.Coxeter.Length


namespace HeckeAlgebra

variable {B : Type*} {W : Type*} [Group W] {M : CoxeterMatrix B}

/-- The pair of scalars $(a_s, b_s)_{s ∈ B}$ defining the quadratic relation
$T_s^2 = a_s T_s + b_s T_1$ for a generic Hecke algebra. -/
structure StructureConstants (B : Type*) (R : Type*) [CommRing R] where
  a : B → R
  b : B → R

end HeckeAlgebra
