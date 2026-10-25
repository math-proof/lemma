/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SkewPrimitiveCategorical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.FGModuleCat.Basic
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Spectrum.Maximal.Basic
import Def.v1.Atlas.TensorCategories.code.SkewPrimitiveCategorical.Part3
set_option maxHeartbeats 800000

open Coalgebra
open scoped TensorProduct
open CategoryTheory MonoidalCategory Category Limits

universe v u w


noncomputable section

section ComoduleExt

variable {k : Type u} {C : Type u} [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]

/-- Reflexivity of comodule extension equivalence. -/
theorem ComoduleExtension.Equiv.refl {g h : C} (E : ComoduleExtension (k := k) g h) :
    ComoduleExtension.Equiv E E := by
  unfold ComoduleExtension.Equiv
  simp [trivialSkewPrimitiveSubspace]

/-- Symmetry of comodule extension equivalence. -/
theorem ComoduleExtension.Equiv.symm {g h : C}
    {E₁ E₂ : ComoduleExtension (k := k) g h} (h_eq : ComoduleExtension.Equiv E₁ E₂) :
    ComoduleExtension.Equiv E₂ E₁ := by
  unfold ComoduleExtension.Equiv at *
  rwa [show E₂.x - E₁.x = -(E₁.x - E₂.x) from (neg_sub E₁.x E₂.x).symm, neg_mem_iff]

/-- Transitivity of comodule extension equivalence. -/
theorem ComoduleExtension.Equiv.trans {g h : C}
    {E₁ E₂ E₃ : ComoduleExtension (k := k) g h}
    (h₁₂ : ComoduleExtension.Equiv E₁ E₂) (h₂₃ : ComoduleExtension.Equiv E₂ E₃) :
    ComoduleExtension.Equiv E₁ E₃ := by
  unfold ComoduleExtension.Equiv at *
  have : E₁.x - E₃.x = (E₁.x - E₂.x) + (E₂.x - E₃.x) := by abel
  rw [this]
  exact Submodule.add_mem _ h₁₂ h₂₃

end ComoduleExt
end
