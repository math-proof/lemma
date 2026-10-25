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
import Theorem.v1.Atlas.TensorCategories.code.QuantumSl2Instance
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

/-- The candidate comultiplication of `K`: `K ⊗ K`. -/
noncomputable def DeltaK : A ⊗[k] A := KK ⊗ₜ[k] KK

/-- The candidate comultiplication of `E`: `E ⊗ K + 1 ⊗ E`. -/
noncomputable def DeltaE : A ⊗[k] A := EE ⊗ₜ[k] KK + 1 ⊗ₜ[k] EE

/-- The candidate comultiplication of `F`: `F ⊗ 1 + K^{-1} ⊗ F`. -/
noncomputable def DeltaF : A ⊗[k] A := FF ⊗ₜ[k] 1 + Kinv ⊗ₜ[k] FF

end SmallQuantumSl2Instance
