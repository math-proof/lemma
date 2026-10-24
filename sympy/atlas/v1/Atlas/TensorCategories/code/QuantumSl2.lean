/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Coalgebra.TensorProduct

set_option maxHeartbeats 400000

open Coalgebra HopfAlgebra
open scoped TensorProduct

universe u v


section Def_1_24_2

variable (R : Type*) [CommRing R] (H : Type*) [Ring H] [Bialgebra R H]

/-- An element `x` of a bialgebra `H` is primitive if `Δ(x) = x ⊗ 1 + 1 ⊗ x`
(Definition 1.24.2 of Etingof–Gelaki–Nikshych–Ostrik). -/
def IsPrimitiveElement (x : H) : Prop :=
  Coalgebra.comul (R := R) x = x ⊗ₜ[R] 1 + 1 ⊗ₜ[R] x

/-- The submodule `Prim(H)` of primitive elements of a bialgebra `H`. -/
def primitiveElements : Submodule R H where
  carrier := {x : H | IsPrimitiveElement R H x}
  add_mem' {x y} (hx : IsPrimitiveElement R H x) (hy : IsPrimitiveElement R H y) := by
    show IsPrimitiveElement R H (x + y)
    unfold IsPrimitiveElement at *
    rw [map_add, hx, hy, TensorProduct.add_tmul, TensorProduct.tmul_add]
    abel
  zero_mem' := by
    show IsPrimitiveElement R H 0
    simp [IsPrimitiveElement, TensorProduct.zero_tmul, TensorProduct.tmul_zero]
  smul_mem' r x (hx : IsPrimitiveElement R H x) := by
    show IsPrimitiveElement R H (r • x)
    unfold IsPrimitiveElement at *
    rw [LinearMap.map_smul, hx]
    simp [TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_add]

end Def_1_24_2


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

/-- Reference abbreviation for Definition 1.25.1: the quantum group `U_q(sl_2)`. -/
abbrev Definition_1_25_1 (k : Type u) [Field k] (A : Type v) [Ring A] [HopfAlgebra k A] :=
  QuantumSl2 k A

namespace QuantumSl2

variable {k : Type u} [Field k] {A : Type v} [Ring A] [HopfAlgebra k A] [h : QuantumSl2 k A]


/-- The Cartan-type element `(q - q^{-1})^{-1} · (K - K^{-1})` of the quantum group. -/
noncomputable def cartanElement : A :=
  (h.q - (h.q)⁻¹)⁻¹ • (h.K - h.Kinv)
