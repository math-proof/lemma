/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2Instance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.TensorCategories.code.QuantumSl2Concrete.Part5
import Lemma.Category.Atlas.v1.TensorCategories.code.QuantumSl2Concrete
import Lemma.Category.Atlas.v1.TensorCategories.code.QBinomial
import Theorem.v1.Atlas.TensorCategories.code.QBinomial.Part2
import Theorem.v1.Atlas.TensorCategories.code.QuantumSl2Instance.Part2
open Coalgebra HopfAlgebra
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 800000


namespace SmallQuantumSl2Instance

variable (n : ℕ) (k : Type*) [Field k] (q : k)

local notation "A" => SmallQuantumSl2Alg n k q

local notation "KK" => SmallQuantumSl2Alg.K n k q

local notation "EE" => SmallQuantumSl2Alg.E n k q

local notation "FF" => SmallQuantumSl2Alg.F n k q

local notation "Kinv" => SmallQuantumSl2Alg.Kinv n k q

variable [hyp : QuantumSl2Hypotheses n k q]

include hyp

/-- The candidate comultiplication on `SmallQuantumSl2Alg`, obtained by lifting
the prescribed values `DeltaK, DeltaE, DeltaF` through the universal property. -/
noncomputable def comulHomAux :
    A →ₐ[k] A ⊗[k] A :=
  SmallQuantumSl2Alg.lift n k q
    (DeltaK n k q) (DeltaE n k q) (DeltaF n k q)
    (DeltaK_pow_n n k q) (DeltaE_pow_n n k q) (DeltaF_pow_n n k q)
    (DeltaKE_comm n k q) (DeltaKF_comm n k q)
    (DeltaEF_comm n k q)

/-- The candidate counit on `SmallQuantumSl2Alg`: `K ↦ 1`, `E ↦ 0`, `F ↦ 0`. -/
noncomputable def counitHomAux : A →ₐ[k] k :=
  SmallQuantumSl2Alg.lift n k q (1 : k) (0 : k) (0 : k)
    (by simp)
    (by simp [n_ne_zero n k q])
    (by simp [n_ne_zero n k q])
    (by simp) (by simp) (by simp)

end SmallQuantumSl2Instance
