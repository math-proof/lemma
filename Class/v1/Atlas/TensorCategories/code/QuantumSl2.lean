/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Coalgebra.TensorProduct
import Def.v1.Atlas.TensorCategories.code.QuantumSl2
set_option maxHeartbeats 400000

open Coalgebra HopfAlgebra
open scoped TensorProduct

universe u v


/-- A `QuantumSl2 k A` structure bundles the quantum group `U_q(sl_2)` data on a
`k`-Hopf algebra `A`: a parameter `q ≠ 0` with `q^2 ≠ 1`, generators `K, E, F`
and an inverse `Kinv` of `K`, the standard Drinfeld–Jimbo relations
`KEK^{-1} = q^2 E`, `KFK^{-1} = q^{-2} F`, `[E, F] = (K - K^{-1})/(q - q^{-1})`,
and the standard formulas for the comultiplication, counit and antipode on the
generators. -/
class QuantumSl2 (k : Type u) [Field k] (A : Type v) [Ring A] [HopfAlgebra k A] where
  q : k
  hq_ne_zero : q ≠ 0
  hq_sq_ne_one : q ^ 2 ≠ 1
  K : A
  Kinv : A
  E : A
  F : A
  K_mul_Kinv : K * Kinv = 1
  Kinv_mul_K : Kinv * K = 1
  K_E_Kinv : K * E * Kinv = q ^ 2 • E
  K_F_Kinv : K * F * Kinv = (q ^ 2)⁻¹ • F
  EF_comm : E * F - F * E = (q - q⁻¹)⁻¹ • (K - Kinv)
  comul_K : comul (R := k) K = K ⊗ₜ[k] K
  comul_E : comul (R := k) E = E ⊗ₜ[k] K + 1 ⊗ₜ[k] E
  comul_F : comul (R := k) F = F ⊗ₜ[k] 1 + Kinv ⊗ₜ[k] F
  counit_K : counit (R := k) K = (1 : k)
  counit_E : counit (R := k) E = (0 : k)
  counit_F : counit (R := k) F = (0 : k)
  antipode_K : antipode k K = Kinv
  antipode_E : antipode k E = -(E * Kinv)
  antipode_F : antipode k F = -(K * F)

