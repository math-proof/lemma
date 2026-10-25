/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/VecInstances.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Abbrev.v1.Atlas.TensorCategories.code.TensorCategoryDef.Part3
import Lemma.Category.Atlas.v1.TensorCategories.code.TensorCategoryDef
import Theorem.v1.Atlas.TensorCategories.code.VecInstances
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Limits

universe v u


noncomputable section

namespace VecInstances

section FiniteLength

variable (k : Type u) [Field k]

/-- The order embedding from subobjects of `X` in `Vec k` to submodules of the
underlying `k`-module, built by composing the forgetful functor with mathlib's
`subobjectModule` equivalence. -/
def subobjectOrderEmbedding (X : Vec k) :
    Subobject X ↪o Submodule k X :=
  let F := forget₂ (FGModuleCat k) (ModuleCat k)
  let ff : F.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful F

  let e₁ : Subobject X ↪o Subobject (F.obj X) :=
    OrderEmbedding.ofMapLEIff
      (fun s => Subobject.mk (F.map s.arrow))
      (fun s₁ s₂ => by
        constructor
        ·

          intro h
          let g := Subobject.ofMkLEMk (F.map s₁.arrow) (F.map s₂.arrow) h
          let g' := ff.preimage g
          apply Subobject.le_of_comm g'
          apply F.map_injective
          rw [F.map_comp, ff.map_preimage]
          exact Subobject.ofMkLEMk_comp h
        ·

          intro h
          let g := Subobject.ofLE _ _ h
          refine Subobject.mk_le_mk_of_comm (F.map g) ?_
          rw [← F.map_comp, Subobject.ofLE_arrow])

  e₁.trans (ModuleCat.subobjectModule (F.obj X)).toOrderEmbedding

end FiniteLength
end VecInstances
end
