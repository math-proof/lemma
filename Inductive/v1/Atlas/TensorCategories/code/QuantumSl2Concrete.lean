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
public import Theorem.v1.Atlas.TensorCategories.code.QuantumSl2Concrete.Part2
variable {n : ℕ} {k : Type*} [Field k]

namespace SmallQuantumSl2

/-- Relations defining the small quantum `sl_2` algebra `u_q(sl_2)` of dimension `n`:
nilpotency relations `K^n = 1`, `E^n = 0`, `F^n = 0` together with the `q`-commutation
relations between `K, E, F` adapted to the small quantum group setting. -/
public inductive SmallQuantumRel (n : ℕ) (k : Type*) [Field k] (q : k) :
    FreeAlgebra k (Fin 3) → FreeAlgebra k (Fin 3) → Prop where
  | K_pow_n : SmallQuantumRel n k q
      ((FreeAlgebra.ι k (0 : Fin 3)) ^ n) 1
  | E_pow_n : SmallQuantumRel n k q
      ((FreeAlgebra.ι k (1 : Fin 3)) ^ n) 0
  | F_pow_n : SmallQuantumRel n k q
      ((FreeAlgebra.ι k (2 : Fin 3)) ^ n) 0
  | KE_comm : SmallQuantumRel n k q
      (FreeAlgebra.ι k (0 : Fin 3) * FreeAlgebra.ι k (1 : Fin 3))
      (q ^ 2 • (FreeAlgebra.ι k (1 : Fin 3) * FreeAlgebra.ι k (0 : Fin 3)))
  | KF_comm : SmallQuantumRel n k q
      (FreeAlgebra.ι k (0 : Fin 3) * FreeAlgebra.ι k (2 : Fin 3))
      ((q ^ 2)⁻¹ • (FreeAlgebra.ι k (2 : Fin 3) * FreeAlgebra.ι k (0 : Fin 3)))
  | EF_comm : SmallQuantumRel n k q
      (FreeAlgebra.ι k (1 : Fin 3) * FreeAlgebra.ι k (2 : Fin 3) -
       FreeAlgebra.ι k (2 : Fin 3) * FreeAlgebra.ι k (1 : Fin 3))
      ((q - q⁻¹)⁻¹ • (FreeAlgebra.ι k (0 : Fin 3) -
       FreeAlgebra.ι k (0 : Fin 3) ^ (n - 1)))

end SmallQuantumSl2
