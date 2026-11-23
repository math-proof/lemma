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
public import Theorem.v1.Atlas.TensorCategories.code.QuantumSl2Concrete.Part3

@[expose] public section

variable {n : ℕ} {k : Type*} [Field k]


namespace SmallQuantumSl2

variable (n : ℕ) (k : Type*) [Field k] (q : k)

namespace SmallQuantumSl2Alg

/-- Universal property of `SmallQuantumSl2Alg`: any choice of images `K', E', F'`
in a `k`-algebra `A` satisfying the small quantum relations extends uniquely to
a `k`-algebra homomorphism from `SmallQuantumSl2Alg n k q`. -/
noncomputable def lift {A : Type*} [Ring A] [Algebra k A]
    (K' E' F' : A)
    (hK : K' ^ n = 1)
    (hE : E' ^ n = 0)
    (hF : F' ^ n = 0)
    (hKE : K' * E' = q ^ 2 • (E' * K'))
    (hKF : K' * F' = (q ^ 2)⁻¹ • (F' * K'))
    (hEF : E' * F' - F' * E' = (q - q⁻¹)⁻¹ • (K' - K' ^ (n - 1))) :
    SmallQuantumSl2Alg n k q →ₐ[k] A :=
  (RingQuot.liftAlgHom k).toFun
    ⟨FreeAlgebra.lift k (fun i => match i with | 0 => K' | 1 => E' | 2 => F'), by
      intro a b hab
      cases hab with
      | K_pow_n =>
        simp [map_pow, map_one, FreeAlgebra.lift_ι_apply, hK]
      | E_pow_n =>
        simp [map_pow, map_zero, FreeAlgebra.lift_ι_apply, hE]
      | F_pow_n =>
        simp [map_pow, map_zero, FreeAlgebra.lift_ι_apply, hF]
      | KE_comm =>
        simp [map_mul, map_smul, FreeAlgebra.lift_ι_apply, hKE]
      | KF_comm =>
        simp [map_mul, map_smul, FreeAlgebra.lift_ι_apply, hKF]
      | EF_comm =>
        simp [map_mul, map_sub, map_smul, map_pow, FreeAlgebra.lift_ι_apply, hEF]⟩

end SmallQuantumSl2Alg
end SmallQuantumSl2
