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
import Def.v1.Atlas.TensorCategories.code.QuasiBialgebra.Part3
set_option maxHeartbeats 800000

open scoped TensorProduct

universe u v


/-- A twist for a quasi-bialgebra `H`: an invertible element `J ∈ H ⊗ H` with
`(ε ⊗ Id)(J) = (Id ⊗ ε)(J) = 1` (Definition 1.34.6). -/
structure QuasiBialgebraTwist (R : Type u) (H : Type v)
    [CommSemiring R] [Semiring H] [Algebra R H]
    [QuasiBialgebra R H] where
  J : (H ⊗[R] H)ˣ
  counit_left :
    QuasiBialgebraTwist.counitTensorId R H (QuasiBialgebra.counit) (J : H ⊗[R] H) = 1
  counit_right :
    QuasiBialgebraTwist.idTensorCounit R H (QuasiBialgebra.counit) (J : H ⊗[R] H) = 1

