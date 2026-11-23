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
public import Inductive.v1.Atlas.TensorCategories.code.QuantumSl2Concrete
@[expose] public section

variable {n : ℕ} {k : Type*} [Field k]


namespace SmallQuantumSl2

/-- The small quantum `sl_2` algebra: the quotient of the free `k`-algebra on
three generators by the small quantum relations `SmallQuantumRel n k q`. -/
abbrev SmallQuantumSl2Alg (n : ℕ) (k : Type*) [Field k] (q : k) :=
  RingQuot (SmallQuantumRel n k q)

variable (n : ℕ) (k : Type*) [Field k] (q : k)

namespace SmallQuantumSl2Alg

/-- The canonical algebra projection from the free algebra to the small quantum algebra. -/
noncomputable abbrev π : FreeAlgebra k (Fin 3) →ₐ[k] SmallQuantumSl2Alg n k q :=
  RingQuot.mkAlgHom k _

end SmallQuantumSl2Alg
end SmallQuantumSl2
