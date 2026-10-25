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
import Class.v1.Atlas.TensorCategories.code.QuantumSl2Concrete
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
