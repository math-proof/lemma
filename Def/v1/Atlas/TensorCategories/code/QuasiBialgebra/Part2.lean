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
public import Class.v1.Atlas.TensorCategories.code.QuasiBialgebra

@[expose] public section

set_option maxHeartbeats 800000

open scoped TensorProduct

universe u v


/-- Accessor: the associator element `Φ` of a quasi-bialgebra. -/
noncomputable def QuasiBialgebra.associator {R : Type u} {H : Type v}
    [CommSemiring R] [Semiring H] [Algebra R H]
    [qb : QuasiBialgebra R H] : (H ⊗[R] (H ⊗[R] H))ˣ :=
  qb.Φ


