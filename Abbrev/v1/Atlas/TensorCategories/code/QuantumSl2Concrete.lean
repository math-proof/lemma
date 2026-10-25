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
import Inductive.v1.Atlas.TensorCategories.code.QuantumSl2Concrete
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
