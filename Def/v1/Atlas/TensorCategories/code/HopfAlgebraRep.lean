/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HopfAlgebraRep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.TensorCategories.code.HopfAlgebra.Part3
import Lemma.Category.Atlas.v1.TensorCategories.code.HopfAlgebra
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Theorem.v1.Atlas.TensorCategories.code.HopfAlgebraRep
open CategoryTheory Coalgebra Bialgebra
open scoped TensorProduct

universe u


section ComulAction

variable (k : Type u) [CommRing k] (H : Type u) [Ring H] [Bialgebra k H]

/-- The counit of a bialgebra `H` as a `k`-algebra homomorphism `H →ₐ[k] k`. -/
def RepBialgebra.counitAlgHom : H →ₐ[k] k := Bialgebra.counitAlgHom k H

/-- The trivial `H`-module structure on `k`, obtained by letting `H` act through its counit. -/
@[reducible]
noncomputable def RepBialgebra.trivialModule : Module H k :=
  Module.compHom k (Bialgebra.counitAlgHom k H).toRingHom

end ComulAction
