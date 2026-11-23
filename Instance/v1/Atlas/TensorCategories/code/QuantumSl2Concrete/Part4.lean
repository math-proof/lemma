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
public import Class.v1.Atlas.TensorCategories.code.QuantumSl2Concrete
@[expose] public section

variable {n : ℕ} {k : Type*} [Field k]


namespace SmallQuantumSl2

variable (n : ℕ) (k : Type*) [Field k] (q : k)

open Coalgebra HopfAlgebra

open scoped TensorProduct

set_option synthInstance.maxHeartbeats 800000

namespace SmallQuantumSl2Alg

variable {n : ℕ} {k : Type*} [Field k] {q : k}

/-- Given `SmallQuantumSl2HopfData`, the small quantum algebra becomes a `k`-bialgebra. -/
noncomputable instance instBialgebra [hd : SmallQuantumSl2HopfData n k q] :
    Bialgebra k (SmallQuantumSl2Alg n k q) :=
  Bialgebra.ofAlgHom hd.comulHom hd.counitHom
    hd.coassoc_axiom hd.rTensor_counit_axiom hd.lTensor_counit_axiom

/-- Given `SmallQuantumSl2HopfData`, the small quantum algebra becomes a `k`-Hopf algebra. -/
noncomputable instance instHopfAlgebra [hd : SmallQuantumSl2HopfData n k q] :
    HopfAlgebra k (SmallQuantumSl2Alg n k q) := by
  letI : HopfAlgebraStruct k (SmallQuantumSl2Alg n k q) := ⟨hd.antipodeLin⟩
  exact HopfAlgebra.mk hd.mul_antipode_rTensor_axiom hd.mul_antipode_lTensor_axiom

end SmallQuantumSl2Alg
end SmallQuantumSl2
