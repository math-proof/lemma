/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuasiBialgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Def.v1.Atlas.TensorCategories.code.QuasiBialgebra.Part3
public section

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

