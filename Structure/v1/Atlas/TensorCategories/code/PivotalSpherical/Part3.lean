/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/PivotalSpherical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Abbrev.v1.Atlas.TensorCategories.code.PivotalSpherical.Part3
set_option maxHeartbeats 800000

set_option autoImplicit false

open CategoryTheory MonoidalCategory Category Limits

universe w v u


namespace TensorCategories

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

/-- EGNO Proposition 1.37.3: both left and right quantum traces are additive on short
exact sequences of objects compatible with the chosen morphisms to the double duals. -/
structure Proposition_1_37_3 : Prop where
  left_additive : ∀ [Preadditive C] {V W Q : C}
    (i : W ⟶ V) (p : V ⟶ Q)
    (aV : V ⟶ (Vᘁ)ᘁ) (aW : W ⟶ (Wᘁ)ᘁ) (aQ : Q ⟶ (Qᘁ)ᘁ)
    (_ : Mono i) (_ : Epi p)
    (_ : i ≫ p = 0)
    (_ : i ≫ aV = aW ≫ (iᘁ)ᘁ)
    (_ : p ≫ aQ = aV ≫ (pᘁ)ᘁ),
    leftQuantumTrace C aV = leftQuantumTrace C aW + leftQuantumTrace C aQ
  right_additive : ∀ [Preadditive C] {V W Q : C}
    (i : W ⟶ V) (p : V ⟶ Q)
    (aV : V ⟶ ᘁ(ᘁV)) (aW : W ⟶ ᘁ(ᘁW)) (aQ : Q ⟶ ᘁ(ᘁQ))
    (_ : Mono i) (_ : Epi p)
    (_ : i ≫ p = 0)
    (_ : i ≫ aV = aW ≫ leftAdjointMate (leftAdjointMate i))
    (_ : p ≫ aQ = aV ≫ leftAdjointMate (leftAdjointMate p)),
    rightQuantumTrace C aV = rightQuantumTrace C aW + rightQuantumTrace C aQ

end TensorCategories
