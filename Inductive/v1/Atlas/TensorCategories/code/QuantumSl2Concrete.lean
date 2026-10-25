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
import Theorem.v1.Atlas.TensorCategories.code.QuantumSl2Concrete.Part2
variable {n : ℕ} {k : Type*} [Field k]


namespace SmallQuantumSl2

/-- Relations defining the small quantum `sl_2` algebra `u_q(sl_2)` of dimension `n`:
nilpotency relations `K^n = 1`, `E^n = 0`, `F^n = 0` together with the `q`-commutation
relations between `K, E, F` adapted to the small quantum group setting. -/
inductive SmallQuantumRel (n : ℕ) (k : Type*) [Field k] (q : k) :
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
