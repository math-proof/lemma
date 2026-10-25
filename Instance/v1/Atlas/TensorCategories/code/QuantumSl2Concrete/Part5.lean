/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2Concrete.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.Algebra.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.RingQuot
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Def.v1.Atlas.TensorCategories.code.QuantumSl2.Part2
import Lemma.Category.Atlas.v1.TensorCategories.code.QuantumSl2
import Theorem.v1.Atlas.TensorCategories.code.QuantumSl2Concrete.Part4
variable {n : ℕ} {k : Type*} [Field k]


namespace SmallQuantumSl2

variable (n : ℕ) (k : Type*) [Field k] (q : k)

open Coalgebra HopfAlgebra

open scoped TensorProduct

set_option synthInstance.maxHeartbeats 800000

namespace SmallQuantumSl2Alg

variable {n : ℕ} {k : Type*} [Field k] {q : k}

/-- Given Hopf data and `n ≥ 2`, `q ≠ 0`, `q^2 ≠ 1`, the small quantum algebra
`SmallQuantumSl2Alg n k q` is a `QuantumSl2`. -/
noncomputable instance instQuantumSl2
    [hd : SmallQuantumSl2HopfData n k q]
    (hn : 2 ≤ n) (hq : q ≠ 0) (hq2 : q ^ 2 ≠ 1) :
    QuantumSl2 k (SmallQuantumSl2Alg n k q) where
  q := q
  hq_ne_zero := hq
  hq_sq_ne_one := hq2
  K := K n k q
  Kinv := Kinv n k q
  E := E n k q
  F := F n k q
  K_mul_Kinv := K_mul_Kinv n k q (Nat.one_le_of_lt (Nat.lt_of_lt_of_le one_lt_two hn))
  Kinv_mul_K := Kinv_mul_K n k q (Nat.one_le_of_lt (Nat.lt_of_lt_of_le one_lt_two hn))
  K_E_Kinv := by

    have hKE := K_mul_E_eq n k q
    have hKKinv := K_mul_Kinv n k q (Nat.one_le_of_lt (Nat.lt_of_lt_of_le one_lt_two hn))
    rw [hKE, smul_mul_assoc, mul_assoc, hKKinv, mul_one]
  K_F_Kinv := by

    have hKF := K_mul_F_eq n k q
    have hKKinv := K_mul_Kinv n k q (Nat.one_le_of_lt (Nat.lt_of_lt_of_le one_lt_two hn))
    rw [hKF, smul_mul_assoc, mul_assoc, hKKinv, mul_one]
  EF_comm := E_mul_F_comm n k q
  comul_K := by rw [comul_eq]; exact hd.comulHom_K
  comul_E := by rw [comul_eq]; exact hd.comulHom_E
  comul_F := by rw [comul_eq]; exact hd.comulHom_F
  counit_K := by rw [counit_eq]; exact hd.counitHom_K
  counit_E := by rw [counit_eq]; exact hd.counitHom_E
  counit_F := by rw [counit_eq]; exact hd.counitHom_F
  antipode_K := by rw [antipode_eq]; exact hd.antipodeLin_K
  antipode_E := by rw [antipode_eq]; exact hd.antipodeLin_E
  antipode_F := by rw [antipode_eq]; exact hd.antipodeLin_F

end SmallQuantumSl2Alg
end SmallQuantumSl2
