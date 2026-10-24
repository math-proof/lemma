/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CoradicalFiltration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.TensorCategories.code.CoalgebraBialgebra
import Lemma.Category.Atlas.v1.TensorCategories.code.CoalgebraBialgebra
import Lemma.Category.Atlas.v1.TensorCategories.code.HopfAlgebra
import Lemma.Category.Atlas.v1.TensorCategories.code.FiniteTensorCategory
import sympy.atlas.v1.Atlas.TensorCategories.code.HopfAlgebra
import sympy.atlas.v1.Atlas.TensorCategories.code.FiniteTensorCategory
import Mathlib.Algebra.Algebra.Operations
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.CategoryTheory.Simple
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Coalgebra.GroupLike
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.RingTheory.Coalgebra.Hom

set_option maxHeartbeats 400000

open scoped TensorProduct
open Coalgebra

universe u v

variable {R : Type u} {C : Type v}
variable [CommRing R] [AddCommGroup C] [Module R C] [Coalgebra R C]


namespace Submodule

/-- A submodule `S` of a coalgebra `C` is a subcoalgebra if it is closed under the
comultiplication: `comul(S) ⊆ S ⊗ S`. -/
def IsSubcoalgebra (S : Submodule R C) : Prop :=
  ∀ a ∈ S, Coalgebra.comul (R := R) a ∈ Submodule.map₂ (TensorProduct.mk R C C) S S

/-- A submodule `S` is a simple subcoalgebra if it is nonzero, is a subcoalgebra, and has
no proper nonzero sub-subcoalgebra. -/
def IsSimpleCoalgebra (S : Submodule R C) : Prop :=
  S ≠ ⊥ ∧ S.IsSubcoalgebra ∧
    ∀ T : Submodule R C, T.IsSubcoalgebra → T ≤ S → T = ⊥ ∨ T = S


/-- The coradical of a coalgebra `C`: the sum of all simple subcoalgebras of `C`. -/
noncomputable def coradical : Submodule R C :=
  ⨆ (S : Submodule R C) (_ : S.IsSimpleCoalgebra), S


/-- The coradical filtration `C_0 ⊆ C_1 ⊆ ⋯` of a coalgebra `C`: `C_0` is the coradical
and `C_{n+1}` is the preimage under `comul` of `C_n ⊗ C + C ⊗ C_0`. -/
noncomputable def coradicalFiltration : ℕ → Submodule R C
  | 0 => coradical
  | n + 1 =>
    (Submodule.map₂ (TensorProduct.mk R C C) (coradicalFiltration n) ⊤ ⊔
     Submodule.map₂ (TensorProduct.mk R C C) ⊤ coradical).comap
      (Coalgebra.comul (R := R))

/-- A grouplike element of a coalgebra: an element `g` satisfying `Δ(g) = g ⊗ g` and
`ε(g) = 1`. -/
def IsGrouplike (g : C) : Prop :=
  Coalgebra.comul (R := R) g = g ⊗ₜ g ∧ Coalgebra.counit (R := R) g = 1

/-- The set of grouplike elements of `C`. -/
def grouplikes : Set C := {g : C | IsGrouplike (R := R) g}

/-- An `(g, h)`-skew primitive element: `x ∈ C` such that `Δ(x) = x ⊗ g + h ⊗ x`. -/
def IsSkewPrimitive (g h x : C) : Prop :=
  Coalgebra.comul (R := R) x = x ⊗ₜ g + h ⊗ₜ x

/-- The submodule of `(g, h)`-skew primitive elements of `C`. -/
def skewPrimitiveSpace (g h : C) : Submodule R C where
  carrier := {x : C | IsSkewPrimitive (R := R) g h x}
  add_mem' {x y} (hx : IsSkewPrimitive g h x) (hy : IsSkewPrimitive g h y) := by
    show IsSkewPrimitive (R := R) g h (x + y)
    unfold IsSkewPrimitive at *
    rw [map_add, hx, hy, TensorProduct.add_tmul, TensorProduct.tmul_add]
    abel
  zero_mem' := by
    show IsSkewPrimitive (R := R) g h 0
    simp [IsSkewPrimitive, TensorProduct.zero_tmul, TensorProduct.tmul_zero]
  smul_mem' r x (hx : IsSkewPrimitive g h x) := by
    show IsSkewPrimitive (R := R) g h (r • x)
    unfold IsSkewPrimitive at *
    rw [LinearMap.map_smul, hx]
    simp [TensorProduct.smul_tmul', TensorProduct.tmul_smul]


/-- A coalgebra is cosemisimple if its coradical is the entire coalgebra. -/
def IsCosemisimple : Prop := coradical (R := R) (C := C) = ⊤

/-- Definition 1.29.3 (EGNO): a coalgebra `C` is cosemisimple iff `C_0 = C`. -/
abbrev def_1_29_3 := @IsCosemisimple R C _ _ _ _

/-- A coalgebra `C` is pointed if every simple subcoalgebra of `C` is one-dimensional, i.e.
spanned by a grouplike element. -/
def IsPointedCoalgebra : Prop :=
  ∀ S : Submodule R C, S.IsSimpleCoalgebra →
    ∃ g : C, S = Submodule.span R {g}


/-- The submodule `∑_{i+j=n} C_i ⊗ C_j ⊆ C ⊗ C` used to formulate the comultiplication
compatibility of the coradical filtration. -/
noncomputable def filtrationTensorSum (n : ℕ) : Submodule R (C ⊗[R] C) :=
  ⨆ (i : Fin (n + 1)),
    Submodule.map₂ (TensorProduct.mk R C C)
      (coradicalFiltration i.val) (coradicalFiltration (n - i.val))

/-- The right slice operator on `C` associated to a functional `f : C → R`: applies
`comul` then contracts the right factor through `f`. -/
noncomputable def coalgebraRightSlice (f : C →ₗ[R] R) : C →ₗ[R] C :=
  (TensorProduct.rid R C).toLinearMap.comp
    ((LinearMap.lTensor C f).comp (Coalgebra.comul (R := R)))

/-- The left slice operator on `C` associated to a functional `f : C → R`: applies
`comul` then contracts the left factor through `f`. -/
noncomputable def coalgebraLeftSlice (f : C →ₗ[R] R) : C →ₗ[R] C :=
  (TensorProduct.lid R C).toLinearMap.comp
    ((LinearMap.rTensor C f).comp (Coalgebra.comul (R := R)))

/-- Dual reduction step: if a coalgebra homomorphism `f` is injective on `C_1`, then it is
injective on each level `C_n` of the coradical filtration, via algebra-side surjectivity. -/
def Ext1VanishesForSimples (𝒞 : Type*) [CategoryTheory.Category 𝒞]
    [CategoryTheory.Abelian 𝒞] [CategoryTheory.HasExt 𝒞]
    [CategoryTheory.Limits.HasZeroMorphisms 𝒞] : Prop :=
  ∀ (X Y : 𝒞) [CategoryTheory.Simple X] [CategoryTheory.Simple Y],
    Subsingleton (CategoryTheory.Abelian.Ext X Y 1)

/-- An abelian category is semisimple if `Ext^1` vanishes between all pairs of objects. -/
def IsSemisimpleCat (𝒞 : Type*) [CategoryTheory.Category 𝒞]
    [CategoryTheory.Abelian 𝒞] [CategoryTheory.HasExt 𝒞] : Prop :=
  ∀ (X Y : 𝒞), Subsingleton (CategoryTheory.Abelian.Ext X Y 1)

/-- A locally finite-length category: each non-simple non-zero object admits a short exact
sequence with simple quotient and a strictly shorter subobject. -/
class IsLocallyFiniteLength (𝒞 : Type*) [CategoryTheory.Category 𝒞]
    [CategoryTheory.Abelian 𝒞] where
  length : 𝒞 → ℕ
  exists_ses_simple_quotient : ∀ (Y : 𝒞),
    ¬ CategoryTheory.Limits.IsZero Y → ¬ CategoryTheory.Simple Y →
    ∃ (S : CategoryTheory.ShortComplex 𝒞), S.ShortExact ∧ S.X₂ = Y ∧
      CategoryTheory.Simple S.X₃ ∧ length S.X₁ < length Y

section Prop_1_29_4

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

variable {𝒞 : Type*} [CategoryTheory.Category 𝒞] [CategoryTheory.Abelian 𝒞]
    [CategoryTheory.HasExt 𝒞]

/-- Multiplicativity of the coradical filtration: `C_i · C_j ⊆ C_{i+j}` in a pointed Hopf
algebra over a field. -/
structure IsHopfAlgebraFiltration {R : Type*} {H : Type*}
    [CommRing R] [Ring H] [HopfAlgebra R H]
    (F : ℕ → Submodule R H) : Prop where
  mul_le : ∀ i j : ℕ, F i * F j ≤ F (i + j)
  antipode_eq : ∀ n : ℕ, Submodule.map (HopfAlgebra.antipode R) (F n) = F n

/-- The `n`-th associated graded piece of a filtration `F`: `F n / F (n-1)`, with the
convention that for `n = 0` the bottom level is `⊥`. -/
noncomputable def associatedGraded {R : Type*} {H : Type*}
    [CommRing R] [AddCommGroup H] [Module R H]
    (F : ℕ → Submodule R H) (n : ℕ) : Type _ :=
  ↥(F n) ⧸ (Submodule.comap (F n).subtype (if n = 0 then ⊥ else F (n - 1)))

/-- The coradical filtration of a pointed Hopf algebra over a field is a Hopf-algebra
filtration (Corollary 1.31.5 in EGNO). -/
def IsSemisimpleObject (C : Type*) [Category C] [HasZeroMorphisms C] (X : C) : Prop :=
  ∃ (n : ℕ) (f : Fin n → C) (_ : HasBiproduct f),
    (∀ i, Simple (f i)) ∧ Nonempty (X ≅ @biproduct _ _ _ _ f ‹HasBiproduct f›)

/-- A tensor category is pointed if every simple object has a tensor inverse, i.e.
the simples form a group under `⊗`. -/
class IsPointedTensorCategory (C : Type*) [Category C] [MonoidalCategory C]
    [HasZeroMorphisms C] : Prop where
  simple_has_inverse : ∀ (X : C) [Simple X],
    ∃ (Y : C), Nonempty (X ⊗ Y ≅ 𝟙_ C) ∧ Nonempty (Y ⊗ X ≅ 𝟙_ C)


section AlgebraGeneration

universe u_ag v_ag

variable (R : Type u_ag) (H : Type v_ag)
variable [CommRing R] [AddCommGroup H] [Module R H] [Coalgebra R H]
variable [Ring H] [Algebra R H]

/-- The union of grouplikes and all skew-primitive spaces, viewed as a subset of `H`. -/
def grouplikesAndSkewPrimitives : Set H :=
  grouplikes (R := R) ∪
    ⋃ (g : H) (_ : g ∈ grouplikes (R := R) (C := H))
      (h : H) (_ : h ∈ grouplikes (R := R) (C := H)),
      (skewPrimitiveSpace (R := R) g h : Set H)

/-- `H` is generated as an `R`-algebra by its grouplike and skew-primitive elements. -/
def IsGeneratedByGrouplikesAndSkewPrimitives : Prop :=
  Algebra.adjoin R (grouplikesAndSkewPrimitives R H) = ⊤

end AlgebraGeneration

section Conjecture_1_32

universe u_c v_c

variable (k : Type u_c) (H : Type v_c)
variable [Field k] [CharZero k]
variable [AddCommGroup H] [Module k H] [Coalgebra k H]
variable [Ring H] [Algebra k H]

/-- The Andruskiewitsch-Schneider conjecture: any finite dimensional pointed Hopf algebra
over a field of characteristic zero is generated by its grouplike and skew-primitive
elements (in degree 1 of the coradical filtration). -/
def AndruskiewitschSchneiderConjecture : Prop :=
  FiniteDimensional k H →
  IsPointedCoalgebra (R := k) (C := H) →
  IsGeneratedByGrouplikesAndSkewPrimitives k H

/-- Conjecture 1.32.1 (EGNO): the Andruskiewitsch-Schneider conjecture. -/
abbrev Conjecture_1_32_1 := @AndruskiewitschSchneiderConjecture

end Conjecture_1_32

section TensorGenerated

universe v_tg u_tg

variable {C : Type u_tg} [Category.{v_tg} C]

/-- `Y` is a subquotient of `X` if there exists `Z` with a mono `Z ↪ X` and an epi `Z ↠ Y`. -/
def IsSubquotient (Y X : C) : Prop :=
  ∃ (Z : C) (i : Z ⟶ X) (p : Z ⟶ Y), Mono i ∧ Epi p

variable [MonoidalCategory C] [HasZeroMorphisms C] [HasBinaryBiproducts C]

/-- The tensor-and-biproduct closure of a class `P` of objects: smallest class containing
`P`, the unit object, and closed under tensor product and direct sum. -/
inductive IsInTensorClosure (P : C → Prop) : C → Prop where
  | of_base {X : C} (hX : P X) : IsInTensorClosure P X
  | of_unit : IsInTensorClosure P (𝟙_ C)
  | of_tensor {X Y : C} (hX : IsInTensorClosure P X) (hY : IsInTensorClosure P Y) :
      IsInTensorClosure P (X ⊗ Y)
  | of_directSum {X Y : C} (hX : IsInTensorClosure P X) (hY : IsInTensorClosure P Y) :
      IsInTensorClosure P (X ⊞ Y)

/-- A tensor category is tensor-generated by a class `P` if every object is a subquotient of
a finite direct sum of tensor products of objects in `P`. -/
class IsTensorGenerated (P : C → Prop) : Prop where
  subquotient_of_tensorClosure :
    ∀ (X : C), ∃ (T : C), IsInTensorClosure P T ∧ IsSubquotient X T

/-- Definition 1.32.2 (EGNO): a tensor category `C` is tensor-generated by a collection of
objects `X_α` if every object of `C` is a subquotient of a finite direct sum of tensor
products of `X_α`. -/
abbrev Definition_1_32_2 := @IsTensorGenerated

end TensorGenerated

section LoewyLength2

universe v_ll u_ll

variable (C : Type u_ll) [Category.{v_ll} C]
variable [HasZeroMorphisms C] [HasCokernels C]

/-- An object `X` has Loewy length at most 2 if it admits a semisimple subobject `Y` such
that the cokernel `X/Y` is also semisimple. -/
def HasLoewyLengthAtMostTwo (X : C) : Prop :=
  ∃ (Y : C) (i : Y ⟶ X), Mono i ∧
    IsSemisimpleObject C Y ∧
    IsSemisimpleObject C (cokernel i)

end LoewyLength2

/-- A category `D` is the comodule category of a Hopf algebra `H` over `k`. -/
class IsComoduleCategoryOf (k : Type*) (H : Type*) (D : Type*)
    [CommSemiring k] [Ring H] [HopfAlgebra k H] [Category D] : Prop

/-- Equivalence between "matrix coefficient" / generation-by-grouplikes-and-skew-primitives
characterization on the Hopf algebra side, and tensor-generation by Loewy-length-2 objects
on the comodule category side. -/
section CategoricalConjecture

universe w_cc v_cc u_cc

variable (k : Type w_cc) [Field k] [CharZero k]
variable (C : Type u_cc) [Category.{v_cc} C] [FiniteTensorCategory k C]

/-- Categorical form of the Andruskiewitsch-Schneider conjecture: any finite pointed tensor
category over a field of characteristic zero is tensor-generated by its objects of Loewy
length at most 2. -/
def AndruskiewitschSchneiderCategorical
    [CharZero k] (_hPointed : IsPointedTensorCategory C) : Prop :=
  IsTensorGenerated (fun X => HasLoewyLengthAtMostTwo C X) (C := C)

/-- Conjecture 1.32.4 (EGNO): the categorical Andruskiewitsch-Schneider conjecture about
cocommutative Hopf algebras over algebraically closed fields of characteristic zero. -/
abbrev Conjecture_1_32_4 := @AndruskiewitschSchneiderCategorical

end CategoricalConjecture

section ChevalleyProperty

universe v_cp u_cp

variable (C : Type u_cp) [Category.{v_cp} C] [MonoidalCategory C] [HasZeroMorphisms C]

/-- A tensor category has the Chevalley property if the tensor product of any two
semisimple objects is semisimple. -/
class HasChevalleyProperty : Prop where
  tensor_semisimple : ∀ (X Y : C),
    IsSemisimpleObject C X → IsSemisimpleObject C Y → IsSemisimpleObject C (X ⊗ Y)

/-- Definition 1.31.1 (EGNO): a pointed tensor category has the Chevalley property. -/
def Definition_1_31_1 : Prop := HasChevalleyProperty C

end ChevalleyProperty
