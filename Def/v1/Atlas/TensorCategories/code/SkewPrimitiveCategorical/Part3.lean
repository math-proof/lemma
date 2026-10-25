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
import Structure.v1.Atlas.TensorCategories.code.SkewPrimitiveCategorical
set_option maxHeartbeats 800000

open Coalgebra
open scoped TensorProduct
open CategoryTheory MonoidalCategory Category Limits

universe v u w


noncomputable section

section ComoduleExt

variable {k : Type u} {C : Type u} [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]

/-- Two comodule extensions are equivalent when their witnessing skew-primitives differ by a
trivial skew-primitive multiple of `h - g`. -/
def ComoduleExtension.Equiv {g h : C} (E₁ E₂ : ComoduleExtension (k := k) g h) : Prop :=
  E₁.x - E₂.x ∈ trivialSkewPrimitiveSubspace (k := k) g h

/-- Forget a comodule extension to the underlying skew-primitive element in `skewPrimitiveSpace`. -/
def ComoduleExtension.toSkewPrimitive {g h : C} (E : ComoduleExtension (k := k) g h) :
    skewPrimitiveSpace (R := k) g h :=
  ⟨E.x, E.skew_prim⟩

/-- Convert a skew-primitive element to the corresponding comodule extension. -/
def ComoduleExtension.ofSkewPrimitive {g h : C}
    (p : skewPrimitiveSpace (R := k) g h) : ComoduleExtension (k := k) g h :=
  ⟨p.val, p.property⟩

end ComoduleExt
end
