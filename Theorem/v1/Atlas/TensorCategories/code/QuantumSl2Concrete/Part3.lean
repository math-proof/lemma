/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2Concrete.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Algebra.FreeAlgebra
public import Mathlib.Algebra.RingQuot
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Def.v1.Atlas.TensorCategories.code.QuantumSl2.Part2
public import Theorem.Category.Atlas.v1.TensorCategories.code.QuantumSl2
public import Def.v1.Atlas.TensorCategories.code.QuantumSl2Concrete.Part3

public section

variable {n : ℕ} {k : Type*} [Field k]


namespace SmallQuantumSl2

variable (n : ℕ) (k : Type*) [Field k] (q : k)

namespace SmallQuantumSl2Alg

/-- The defining relation `K^n = 1` in `u_q(sl_2)`. -/
lemma K_pow_n_eq : (K n k q) ^ n = 1 := by
  unfold K; rw [← map_pow, ← map_one (π n k q)]
  exact RingQuot.mkAlgHom_rel k SmallQuantumRel.K_pow_n

/-- The nilpotency relation `E^n = 0` in `u_q(sl_2)`. -/
lemma E_pow_n_eq : (E n k q) ^ n = 0 := by
  unfold E; rw [← map_pow, ← map_zero (π n k q)]
  exact RingQuot.mkAlgHom_rel k SmallQuantumRel.E_pow_n

/-- The nilpotency relation `F^n = 0` in `u_q(sl_2)`. -/
lemma F_pow_n_eq : (F n k q) ^ n = 0 := by
  unfold F; rw [← map_pow, ← map_zero (π n k q)]
  exact RingQuot.mkAlgHom_rel k SmallQuantumRel.F_pow_n

/-- The commutation relation `K E = q^2 (E K)` in `u_q(sl_2)`. -/
lemma K_mul_E_eq :
    K n k q * E n k q = q ^ 2 • (E n k q * K n k q) := by
  unfold K E
  conv_lhs => rw [← map_mul]
  conv_rhs => rw [← map_mul, ← map_smul]
  exact RingQuot.mkAlgHom_rel k SmallQuantumRel.KE_comm

/-- The commutation relation `K F = q^{-2} (F K)` in `u_q(sl_2)`. -/
lemma K_mul_F_eq :
    K n k q * F n k q = (q ^ 2)⁻¹ • (F n k q * K n k q) := by
  unfold K F
  conv_lhs => rw [← map_mul]
  conv_rhs => rw [← map_mul, ← map_smul]
  exact RingQuot.mkAlgHom_rel k SmallQuantumRel.KF_comm

/-- The commutator relation `[E, F] = (K - K^{-1})/(q - q^{-1})` in `u_q(sl_2)`,
written using `K^{n-1}` as the explicit inverse of `K`. -/
lemma E_mul_F_comm :
    E n k q * F n k q - F n k q * E n k q =
    (q - q⁻¹)⁻¹ • (K n k q - K n k q ^ (n - 1)) := by
  unfold K E F
  conv_lhs => rw [← map_mul, ← map_mul, ← map_sub]
  conv_rhs => rw [← map_pow, ← map_sub, ← map_smul]
  exact RingQuot.mkAlgHom_rel k SmallQuantumRel.EF_comm

/-- `K · K^{-1} = 1` (right inverse property) when `1 ≤ n`. -/
lemma K_mul_Kinv (hn : 1 ≤ n) :
    K n k q * Kinv n k q = 1 := by
  unfold Kinv
  have h : n - 1 + 1 = n := Nat.sub_add_cancel hn
  rw [← pow_succ', h]
  exact K_pow_n_eq n k q

/-- `K^{-1} · K = 1` (left inverse property) when `1 ≤ n`. -/
lemma Kinv_mul_K (hn : 1 ≤ n) :
    Kinv n k q * K n k q = 1 := by
  unfold Kinv
  have h : n - 1 + 1 = n := Nat.sub_add_cancel hn
  rw [← pow_succ, h]
  exact K_pow_n_eq n k q

end SmallQuantumSl2Alg
end SmallQuantumSl2
