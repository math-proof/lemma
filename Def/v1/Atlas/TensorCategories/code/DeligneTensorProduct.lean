/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/DeligneTensorProduct.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.TensorCategories.code.DeligneTensorProductDef
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Algebra
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.Algebra.Category.ModuleCat.Abelian
set_option maxHeartbeats 400000


noncomputable section

open TensorProduct CategoryTheory ModuleCat

namespace Deligne

variable (k : Type) [CommRing k]

section ModuleAction

variable (A : Type) [Ring A] [Algebra k A]

variable (B : Type) [Ring B] [Algebra k B]

variable (M : Type) [AddCommGroup M] [Module k M] [Module A M]
  [IsScalarTower k A M] [SMulCommClass k A M]

variable (N : Type) [AddCommGroup N] [Module k N] [Module B N]
  [IsScalarTower k B N] [SMulCommClass k B N]

/-- The `k`-algebra homomorphism `A →ₐ[k] End_k(M ⊗ N)` defined by letting `a ∈ A` act
on the left tensor factor `M`. -/
def actA : A →ₐ[k] Module.End k (M ⊗[k] N) :=
  (Module.End.rTensorAlgHom k M N).comp (Algebra.lsmul k k M)

/-- The `k`-algebra homomorphism `B →ₐ[k] End_k(M ⊗ N)` defined by letting `b ∈ B` act
on the right tensor factor `N`. -/
def actB : B →ₐ[k] Module.End k (M ⊗[k] N) :=
  (Module.End.lTensorAlgHom k N M).comp (Algebra.lsmul k k N)

end ModuleAction
end Deligne
end
