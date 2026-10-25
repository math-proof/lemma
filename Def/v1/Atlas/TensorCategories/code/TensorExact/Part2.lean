/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TensorExact.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.Abelian.Basic
import Theorem.v1.Atlas.TensorCategories.code.TensorExact
set_option maxHeartbeats 400000

open CategoryTheory MonoidalCategory Limits Opposite

universe v u


namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

section ExactFunctors

/-- The left adjoint mate is a bijection `Hom(X, Y) ≃ Hom(ᘁY, ᘁX)` induced by the rigid structure. -/
noncomputable def leftAdjointMateEquiv (X Y : C) : (X ⟶ Y) ≃ ((ᘁY : C) ⟶ (ᘁX : C)) :=
  ((Equiv.mk (fun f => f ≫ (λ_ Y).inv) (fun f => f ≫ (λ_ Y).hom)
      (by intro f; simp) (by intro f; simp)).trans
  (((tensorRightHomEquiv X (ᘁY : C) Y (𝟙_ C)).symm).trans
  (((tensorLeftHomEquiv (ᘁY : C) (ᘁX : C) X (𝟙_ C))).trans
  (Equiv.mk (fun f => f ≫ (ρ_ (ᘁX : C)).hom) (fun f => f ≫ (ρ_ (ᘁX : C)).inv)
      (by intro f; simp) (by intro f; simp)))))

end ExactFunctors
end CategoryTheory
