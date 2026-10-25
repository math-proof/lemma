/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CoradicalFiltration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Abbrev.v1.Atlas.TensorCategories.code.CoalgebraBialgebra.Part4
import Lemma.Category.Atlas.v1.TensorCategories.code.CoalgebraBialgebra
import Lemma.Category.Atlas.v1.TensorCategories.code.HopfAlgebra
import Lemma.Category.Atlas.v1.TensorCategories.code.FiniteTensorCategory
import Theorem.v1.Atlas.TensorCategories.code.HopfAlgebra.Part3
import Instance.v1.Atlas.TensorCategories.code.FiniteTensorCategory.Part8
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

end Submodule
