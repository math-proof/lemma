/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/ExteriorAlgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Ring.CharZero
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.LinearCombination
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Real.Basic
import Def.v1.Atlas.DifferentialGeometry.code.ExteriorAlgebra
open Matrix Finset Module

set_option autoImplicit false


namespace ExteriorAlgebra

variable {R : Type*} [CommRing R] {n : ℕ}

abbrev StrictUpperTriIdx (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

set_option maxHeartbeats 400000 in

abbrev Idx (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

end ExteriorAlgebra
