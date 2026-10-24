/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IntegralsCartanMatrix.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.TensorCategories.code.IntegralsDefs
import Lemma.Category.Atlas.v1.TensorCategories.code.IntegralsDefs
import Lemma.Category.Atlas.v1.TensorCategories.code.DistinguishedInvertible
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import sympy.atlas.v1.Atlas.TensorCategories.code.DistinguishedInvertible
import Mathlib.RingTheory.SimpleModule.Basic

set_option maxHeartbeats 400000

set_option autoImplicit false

open Coalgebra
open scoped TensorProduct

universe u v w


section CartanMatrix

variable {k : Type w} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Reinterpret a `ℕ`-valued Cartan matrix `C_mat` as a matrix over the field `k`
by casting each entry to `k`. -/
def cartanMatrixOverField (C_mat : ι → ι → ℕ) : Matrix ι ι k :=
  Matrix.of (fun i j => (C_mat i j : k))

/-- A rigid monoidal category is unimodular when its distinguished invertible object
`L_ρ` is isomorphic to the unit `𝟙_ C` (Definition 1.52.6). -/
class IsUnimodularCategory (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [RigidCategory C] [HasDistinguishedInvertibleData C] : Prop where
  distinguished_iso_unit : Nonempty (HasDistinguishedInvertibleData.distinguished (C := C) ≅ 𝟙_ C)

/-- The left quantum trace of a morphism `a : V ⟶ V**`, defined as the composition
`coev_V ≫ (a ▷ V*) ≫ ev_{V*}` ending in `𝟙_ C ⟶ 𝟙_ C`. -/
noncomputable def leftQuantumTrace' {V : C} (a : V ⟶ (Vᘁ)ᘁ) : 𝟙_ C ⟶ 𝟙_ C :=
  η_ V (Vᘁ) ≫ (a ▷ Vᘁ) ≫ ε_ (Vᘁ) ((Vᘁ)ᘁ)

/-- Data of a pivotal structure on a rigid monoidal category: a natural isomorphism
`Id ≅ ?**` (Definition 1.38.1). -/
structure PivotalStructureData (C : Type u)
    [Category.{v} C] [MonoidalCategory C] [RigidCategory C] where
  pivotalIso : ∀ (V : C), V ≅ (Vᘁ)ᘁ
  naturality : ∀ {V W : C} (f : V ⟶ W),
    f ≫ (pivotalIso W).hom = (pivotalIso V).hom ≫ (fᘁ)ᘁ

/-- The pivotal dimension of `V` with respect to the pivotal structure `u`, namely
the left quantum trace of `u.pivotalIso V` (Definition 1.38.4). -/
noncomputable def pivotalDim (u : PivotalStructureData C) (V : C) : 𝟙_ C ⟶ 𝟙_ C :=
  leftQuantumTrace' C (u.pivotalIso V).hom

end PivotalDimensionTheorem


section DimProjZero

open CategoryTheory MonoidalCategory

variable {k : Type w} [Field k]
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

/-- A linear functional `l : H → k` is a left cointegral if the convolution identity
`(id ⊗ l) ∘ Δ = η ∘ l` holds, dualizing the notion of a left integral. -/
structure IsLeftCointegral (l : H →ₗ[k] k) : Prop where
  left_cointegral :
    (TensorProduct.rid k H).toLinearMap ∘ₗ l.lTensor H ∘ₗ Coalgebra.comul (R := k) =
    (Algebra.linearMap k H) ∘ₗ l

/-- For a nonzero left cointegral `l` in a finite dimensional `H`, the map sending
`x ∈ H` to `l ∘ mulLeft x` is injective; this is the Frobenius property witnessed by
left cointegrals. -/
end IntegralCointegralPairing


section Proposition1525

open Coalgebra

variable (k : Type u) [Field k] (H : Type v) [Ring H] [Algebra k H] [Coalgebra k H]
