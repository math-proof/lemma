/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Ext1UnitVanishing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import sympy.atlas.v1.Atlas.TensorCategories.code.FiniteTensorCategory
import Lemma.Category.Atlas.v1.TensorCategories.code.FiniteTensorCategory
import Lemma.Category.Atlas.v1.TensorCategories.code.HigherDerivation
import sympy.atlas.v1.Atlas.TensorCategories.code.UnitSemisimplicity
import sympy.atlas.v1.Atlas.TensorCategories.code.HigherDerivation

set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Category Limits

universe v u w

noncomputable section

namespace TensorCategories

section Ext1Def

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The predicate `Ext¹(X, Y) = 0` expressed as: every short exact sequence
`0 → Y → V → X → 0` splits. -/
def Ext1Vanishes (X Y : C) : Prop :=
  ∀ (V : C) (f : Y ⟶ V) (g : V ⟶ X) (hfg : f ≫ g = 0),
    (ShortComplex.mk f g hfg).ShortExact → Nonempty (ShortComplex.mk f g hfg).Splitting

/-- A `k`-linear abelian monoidal category that has enough projectives and finite-
dimensional Hom spaces; this is the underlying ring-category structure used in EGNO. -/
class FiniteRingCategory (k : Type w) [Field k] (C : Type u) [Category.{v} C]
    extends MonoidalCategory C, Abelian C, Linear k C where
  enoughProj : EnoughProjectives C
  homFiniteDim : ∀ (X Y : C), FiniteDimensional k (X ⟶ Y)

section FiniteRingCategoryLemmas

variable (k : Type w) [Field k] (C : Type u) [Category.{v} C] [FiniteRingCategory k C]

/-- Every finite tensor category over `k` carries the underlying structure of a
`FiniteRingCategory` over `k`. -/
instance (priority := 100) FiniteRingCategory.ofFiniteTensorCategory
    (k : Type w) [Field k] (C : Type u) [Category.{v} C]
    [CategoryTheory.FiniteTensorCategory k C] : FiniteRingCategory k C where
  enoughProj := CategoryTheory.FiniteTensorCategory.enoughProj k
  homFiniteDim := CategoryTheory.FiniteTensorCategory.homFiniteDim

section Ext1UnitVanishing

/-- Existence hypothesis: from a non-split extension of `𝟙_ C` by `𝟙_ C` one can build a
higher derivation system on some finite-dimensional `k`-algebra with nonzero first
coefficient `χ 1`. -/
class HasDerivationFromExtension (k : Type w) [Field k] (C : Type u) [Category.{v} C]
    [FiniteRingCategory k C] [Simple (𝟙_ C)] : Prop where
  higher_derivation_from_nonsplit_ext :
    ∀ (V : C) (f : 𝟙_ C ⟶ V) (g : V ⟶ 𝟙_ C) (hfg : f ≫ g = 0),
      (ShortComplex.mk f g hfg).ShortExact →
      ¬ Nonempty (ShortComplex.mk f g hfg).Splitting →
      ∃ (A : Type w) (_ : Ring A) (_ : Algebra k A) (_ : FiniteDimensional k A)
        (ε : A →ₐ[k] k) (hds : HigherDerivationSystem k A ε),
        hds.χ 1 ≠ 0
