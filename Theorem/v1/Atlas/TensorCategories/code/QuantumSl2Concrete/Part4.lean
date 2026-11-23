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
public import Instance.v1.Atlas.TensorCategories.code.QuantumSl2Concrete.Part4

public section

variable {n : ℕ} {k : Type*} [Field k]


namespace SmallQuantumSl2

variable (n : ℕ) (k : Type*) [Field k] (q : k)

open Coalgebra HopfAlgebra

open scoped TensorProduct

set_option synthInstance.maxHeartbeats 800000

namespace SmallQuantumSl2Alg

variable {n : ℕ} {k : Type*} [Field k] {q : k}

/-- The bialgebra `comul` agrees with the comultiplication supplied in `hd`. -/
lemma comul_eq [hd : SmallQuantumSl2HopfData n k q] (x : SmallQuantumSl2Alg n k q) :
    comul (R := k) x = hd.comulHom x := rfl

/-- The bialgebra `counit` agrees with the counit supplied in `hd`. -/
lemma counit_eq [hd : SmallQuantumSl2HopfData n k q] (x : SmallQuantumSl2Alg n k q) :
    counit (R := k) x = hd.counitHom x := rfl

/-- The Hopf algebra `antipode` agrees with the antipode supplied in `hd`. -/
lemma antipode_eq [hd : SmallQuantumSl2HopfData n k q] (x : SmallQuantumSl2Alg n k q) :
    antipode k x = hd.antipodeLin x := rfl

end SmallQuantumSl2Alg
end SmallQuantumSl2
