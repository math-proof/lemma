/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IntegralsCartanMatrix.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Abbrev.v1.Atlas.TensorCategories.code.IntegralsDefs
public import Theorem.Category.Atlas.v1.TensorCategories.code.IntegralsDefs
public import Theorem.Category.Atlas.v1.TensorCategories.code.DistinguishedInvertible
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.CategoryTheory.Simple
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Instance.v1.Atlas.TensorCategories.code.DistinguishedInvertible.Part2
public import Mathlib.RingTheory.SimpleModule.Basic
public import Def.v1.Atlas.TensorCategories.code.IntegralsCartanMatrix.Part3
public section

set_option maxHeartbeats 400000

set_option autoImplicit false

open Coalgebra
open scoped TensorProduct

universe u v w


section DimProjZero

open CategoryTheory MonoidalCategory

variable {k : Type w} [Field k]

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]
variable {H : Type v} [Semiring H] [Algebra k H] [Coalgebra k H]

/-- A linear functional `l : H → k` is a left cointegral if the convolution identity
`(id ⊗ l) ∘ Δ = η ∘ l` holds, dualizing the notion of a left integral. -/
structure IsLeftCointegral (l : H →ₗ[k] k) : Prop where
  left_cointegral :
    (TensorProduct.rid k H).toLinearMap ∘ₗ l.lTensor H ∘ₗ Coalgebra.comul (R := k) =
    (Algebra.linearMap k H) ∘ₗ l

end DimProjZero
