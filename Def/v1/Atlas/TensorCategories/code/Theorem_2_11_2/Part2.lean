/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Theorem_2_11_2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Equivalence
import Structure.v1.Atlas.TensorCategories.code.Theorem_2_11_2.Part3
set_option maxHeartbeats 800000

set_option autoImplicit false

universe v₁ v₂ u₁ u₂


namespace CategoryTheory

open Category MonoidalCategory

attribute [reassoc (attr := simp)] RModHom₂.comm

/-- Step 1 in the proof of Theorem 2.11.2: the natural map sending a morphism
`hom.actOnGen.obj X ⟶ N₂` to its image under `F` is a bijection (Hom on free modules
identifies with Hom in `M`). -/
noncomputable def theorem_2_11_2_equiv
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M]
    (hom : InternalHomData₂ C M)
    (hExact : InternalHomRightExact₂ hom)
    (hGen : InternalHomGeneration₂ hom) :
    M ≌ ModC₂ hom.endAlg := by
  haveI : hom.F.Faithful := step2_faithful₂ hom hExact hGen
  haveI : hom.F.Full := step2_full₂ hom hExact hGen
  haveI : hom.F.EssSurj := step3_essSurj₂ hom hExact hGen
  haveI : hom.F.IsEquivalence := Functor.IsEquivalence.mk
  exact hom.F.asEquivalence

end CategoryTheory
