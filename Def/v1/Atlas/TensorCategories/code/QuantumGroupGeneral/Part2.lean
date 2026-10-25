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
import Structure.v1.Atlas.TensorCategories.code.QuantumGroupGeneral
set_option maxHeartbeats 800000

open Coalgebra HopfAlgebra
open scoped TensorProduct

universe u v


section QAnalogs

variable {k : Type*} [Field k]

namespace CartanDatum

/-- The rank-1 Cartan datum for `sl_2`: Cartan matrix `[2]` with symmetrizer `1`. -/
def sl2 : CartanDatum 1 where
  cartanMatrix := fun _ _ => 2
  symm := fun _ => 1
  diag := fun _ => rfl
  off_diag_nonpos := fun i j hij => absurd (Fin.ext (by omega)) hij
  symm_pos := fun _ => by omega
  symmetrizable := fun _ _ => by ring

end CartanDatum
end QAnalogs
