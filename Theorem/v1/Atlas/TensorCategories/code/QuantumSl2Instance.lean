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
import Class.v1.Atlas.TensorCategories.code.QuantumSl2Instance
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

/-- A primitive `n`-th root of unity (`n ≥ 2`) is nonzero. -/
lemma q_ne_zero : q ≠ 0 := by
  intro h
  have hpow := hyp.hq_prim.pow_eq_one
  have hn := hyp.hn
  rw [h, zero_pow (by omega : n ≠ 0)] at hpow
  exact zero_ne_one hpow

/-- The relation `(q^2)^n = 1`, from primitivity of `q^2`. -/
lemma q2_pow_n : (q ^ 2) ^ n = 1 := hyp.hq2_prim.pow_eq_one

/-- From `n ≥ 2`, `1 < n`. -/
lemma one_lt_n : 1 < n := by have := hyp.hn; omega

/-- From `n ≥ 2`, `1 ≤ n`. -/
lemma one_le_n : 1 ≤ n := by have := hyp.hn; omega

/-- From `n ≥ 2`, `n ≠ 0`. -/
lemma n_ne_zero : n ≠ 0 := by have := hyp.hn; omega

end SmallQuantumSl2Instance
