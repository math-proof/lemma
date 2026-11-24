module
public import Def.v1.Atlas.AlgebraicCombinatorics.code.BooleanCommutator
public import Theorem.Finset.Atlas.v1.AlgebraicCombinatorics.code.BooleanCommutator
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
open Finset BigOperators
set_option autoImplicit false


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/BooleanUpDown.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace BooleanUpDown

variable {n : ℕ}

abbrev Level (n i : ℕ) := { s : Finset (Fin n) // s.card = i }

end BooleanUpDown
