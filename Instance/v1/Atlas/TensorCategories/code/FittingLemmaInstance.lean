/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FittingLemmaInstance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Class.v1.Atlas.TensorCategories.code.FittingLemmaLocalEnd
import Lemma.Category.Atlas.v1.TensorCategories.code.FittingLemmaLocalEnd
import Lemma.Category.Atlas.v1.TensorCategories.code.FittingAlgebraLocalRing
import Theorem.v1.Atlas.TensorCategories.code.FittingAlgebraLocalRing
import Mathlib.CategoryTheory.Idempotents.Basic
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Theorem.v1.Atlas.TensorCategories.code.FittingLemmaInstance
set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents

universe v u w


namespace CategoryTheory

section

variable (k : Type w) [Field k] {C : Type u} [Category.{v} C] [Abelian C] [Linear k C]

/-- In a `k`-linear abelian category with finite-dimensional Hom spaces, every
indecomposable object has a local endomorphism ring. This packages the categorical
Fitting lemma: combine `idem_trivial_of_indecomposable` with the algebraic statement
`isLocalRing_of_finiteDimensional_of_no_nontrivial_idempotents`. -/
noncomputable instance hasLocalEndOfIndecomposable_of_finiteDimensionalEnd
    [∀ (X Y : C), FiniteDimensional k (X ⟶ Y)] :
    FiniteAbelianCategory.HasLocalEndOfIndecomposable k C where
  isLocalRing_end_of_indecomposable P hP := by
    haveI : Nontrivial (End P) :=
      ⟨⟨0, 𝟙 P, fun h => hP.1 (by rw [IsZero.iff_id_eq_zero]; exact h.symm)⟩⟩
    have hfd : FiniteDimensional k (End P) := ‹∀ X Y, FiniteDimensional k (X ⟶ Y)› P P
    exact @isLocalRing_of_finiteDimensional_of_no_nontrivial_idempotents k _ (End P) _ _ _ hfd
      (fun e he => idem_trivial_of_indecomposable hP e he)

end
end CategoryTheory
