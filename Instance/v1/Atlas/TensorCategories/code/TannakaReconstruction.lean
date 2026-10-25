/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TannakaReconstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Category.ModuleCat.Tannaka
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Bialgebra.Basic
import Mathlib.RingTheory.Coalgebra.Basic
import Mathlib.Algebra.Category.FGModuleCat.Basic
import Abbrev.v1.Atlas.TensorCategories.code.QuasiBialgebra
import Abbrev.v1.Atlas.TensorCategories.code.QuasiTensorFunctor.Part5
import Lemma.Category.Atlas.v1.TensorCategories.code.QuasiTensorFunctor
import Def.v1.Atlas.TensorCategories.code.TannakaReconstruction
set_option maxHeartbeats 800000

open CategoryTheory

universe u v w


noncomputable section

variable (k : Type u) [CommRing k] (A : Type u) [Ring A] [Algebra k A]

/-- The `k`-algebra structure on `EndForget₂ A` induced by the central ring homomorphism
`endForget₂AlgebraMap`. -/
instance endForget₂Algebra : Algebra k (EndForget₂ A) :=
  (endForget₂AlgebraMap k A).toAlgebra' (endForget₂_algebraMap_comm k A)

end
