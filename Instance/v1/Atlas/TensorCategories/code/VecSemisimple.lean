/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/VecSemisimple.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Abbrev.v1.Atlas.TensorCategories.code.TensorCategoryDef.Part3
import Lemma.Category.Atlas.v1.TensorCategories.code.TensorCategoryDef
import Lemma.Category.Atlas.v1.TensorCategories.code.VecInstances
import Abbrev.v1.Atlas.TensorCategories.code.VecInstances.Part2
set_option maxHeartbeats 400000

open CategoryTheory MonoidalCategory Limits Module

universe u


noncomputable section

namespace VecSemisimple

variable (k : Type u) [Field k]

/-- The ground field `k`, viewed as a one-dimensional vector space, is a simple
object in `FGModuleCat k`: every monomorphism into it from a nonzero object is an iso. -/
instance simple_of_k : Simple (FGModuleCat.of k k) where
  mono_isIso_iff_nonzero := by
    intro Y f hf
    let F := forget₂ (FGModuleCat k) (ModuleCat k)
    have hFf_mono : Mono (F.map f) := Functor.map_mono F f
    have hSimple : Simple (F.obj (FGModuleCat.of k k)) := by
      change Simple (ModuleCat.of k k); exact simple_of_isSimpleModule
    have h := @Simple.mono_isIso_iff_nonzero _ _ _ _ hSimple _ (F.map f) hFf_mono
    have ff : F.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful F
    rw [show (f ≠ 0) ↔ (F.map f ≠ 0) from by
      constructor
      · intro hne he; apply hne; exact ff.map_injective (by simp [he])
      · intro hne he; apply hne; simp [he]]
    rw [← h]
    exact ⟨fun hiso => F.map_isIso f, fun hiso => ff.isIso_of_isIso_map f⟩

end VecSemisimple
end
