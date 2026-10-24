/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumGroups.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic

set_option maxHeartbeats 800000

universe u v


/-- Definition 1.25.1 (Etingof–Gelaki–Nikshych–Ostrik): The quantum group
`U_q(sl_2)` as the data of generators `E, F` and an invertible `K` in a
`k`-algebra `A`, with `q ≠ ±1`, satisfying `K E K^{-1} = q^2 E`,
`K F K^{-1} = q^{-2} F`, and `[E, F] = (K - K^{-1})/(q - q^{-1})`. -/
structure UqSl2 (k : Type u) [Field k] (A : Type v) [Ring A] [Algebra k A] where
  q : k
  hq_ne_one : q ≠ 1
  hq_ne_neg_one : q ≠ -1
  E : A
  F : A
  K : A
  K_inv : A
  K_mul_K_inv : K * K_inv = 1
  K_inv_mul_K : K_inv * K = 1
  rel_KEKinv : K * E * K_inv = q ^ 2 • E
  rel_KFKinv : K * F * K_inv = (q ^ 2)⁻¹ • F
  rel_EF_comm : E * F - F * E = (q - q⁻¹)⁻¹ • (K - K_inv)

/-- Reference abbreviation for Definition 1.25.1: the quantum group `U_q(sl_2)`. -/
abbrev def_1_25_1 := @UqSl2


section QAnalogs

variable {k : Type*} [Field k]

/-- The q-analog `[n]_q = (q^n - q^{-n})/(q - q^{-1})` of a natural number `n`. -/
noncomputable def qAnalog (q : k) (n : ℕ) : k :=
  (q ^ n - q⁻¹ ^ n) / (q - q⁻¹)

/-- The q-analog factorial `[n]_q! = ∏_{l=1}^{n} [l]_q`. -/
noncomputable def qAnalogFactorial (q : k) (n : ℕ) : k :=
  ∏ l ∈ Finset.range n, qAnalog q (l + 1)

/-- The coefficient `(-1)^l / ([l]_q! · [N-l]_q!)` appearing in the q-Serre relations. -/
noncomputable def qSerreCoeff (q : k) (N l : ℕ) : k :=
  (-1) ^ l / (qAnalogFactorial q l * qAnalogFactorial q (N - l))
