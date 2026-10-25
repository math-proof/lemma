/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumGroupGeneral.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Coalgebra.TensorProduct
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic
import Def.v1.Atlas.TensorCategories.code.QuantumGroupGeneral
set_option maxHeartbeats 800000

open Coalgebra HopfAlgebra
open scoped TensorProduct

universe u v


section QAnalogs

variable {k : Type*} [Field k]

/-- A Cartan datum of rank `r`: a symmetrizable Cartan matrix together with a
choice of symmetrizing positive integers `d_i`. -/
structure CartanDatum (r : ℕ) where
  cartanMatrix : Fin r → Fin r → ℤ
  symm : Fin r → ℕ
  diag : ∀ i, cartanMatrix i i = 2
  off_diag_nonpos : ∀ i j, i ≠ j → cartanMatrix i j ≤ 0
  symm_pos : ∀ i, 0 < symm i
  symmetrizable : ∀ i j, (symm i : ℤ) * cartanMatrix i j = (symm j : ℤ) * cartanMatrix j i

end QAnalogs
