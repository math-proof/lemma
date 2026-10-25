/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuasiBialgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Bialgebra.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Class.v1.Atlas.TensorCategories.code.QuasiBialgebra
set_option maxHeartbeats 800000

open scoped TensorProduct

universe u v


/-- Accessor: the associator element `Φ` of a quasi-bialgebra. -/
noncomputable def QuasiBialgebra.associator {R : Type u} {H : Type v}
    [CommSemiring R] [Semiring H] [Algebra R H]
    [qb : QuasiBialgebra R H] : (H ⊗[R] (H ⊗[R] H))ˣ :=
  qb.Φ


