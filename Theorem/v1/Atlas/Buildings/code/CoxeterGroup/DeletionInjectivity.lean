/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DeletionInjectivity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.CoxeterGroup.DeletionInjectivityHelpers
import Mathlib.GroupTheory.Coxeter.Basic
open CoxeterSystemFromDeletion Function Set


namespace CoxeterSystemFromDeletion

variable {B : Type*} {W : Type*} [Group W]

/-- Compatibility of the canonical homomorphism with word products: $\varphi$
sends the abstract product of a word in simple generators to the concrete
product of the same word under $\mathtt{gen}$. -/
theorem deletionCanonicalHom_map_word_prod
    (gen : B → W) (hgen_inv : ∀ s, gen s * gen s = 1)
    (hgen_ne : ∀ s t, s ≠ t → gen s * gen t ≠ 1)
    (word : List B) :
    let M := deletionCoxeterMatrix gen hgen_inv hgen_ne
    let φ := deletionCanonicalHom gen hgen_inv hgen_ne
    φ ((word.map M.simple).prod) = (word.map gen).prod := by
  intro M φ
  rw [map_list_prod]
  congr 1
  rw [List.map_map]
  congr 1
  ext s
  exact deletionCanonicalHom_apply_simple gen hgen_inv hgen_ne s

/-- Injectivity of the canonical homomorphism: if the family $\mathtt{gen}$
satisfies the deletion condition, generates $W$, and consists of involutions
with no length-2 collapses, then the abstract Coxeter group surjects
isomorphically onto $W$. -/
theorem deletionCanonicalHom_injective
    {B : Type*} {W : Type*} [Group W]
    (gen : B → W) (hgen_inv : ∀ s, gen s * gen s = 1)
    (hgen_ne : ∀ s t, s ≠ t → gen s * gen t ≠ 1)
    (hgen_surj : Subgroup.closure (Set.range gen) = ⊤)
    (hDel : SatisfiesDeletionConditionGen gen) :
    Function.Injective (deletionCanonicalHom gen hgen_inv hgen_ne) := by
  set M := deletionCoxeterMatrix gen hgen_inv hgen_ne
  set φ := deletionCanonicalHom gen hgen_inv hgen_ne
  set cs := M.toCoxeterSystem

  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]

  intro w hw_ker
  rw [MonoidHom.mem_ker] at hw_ker

  obtain ⟨word, rfl⟩ := cs.wordProd_surjective w


  have hφ_word := deletionCanonicalHom_map_word_prod gen hgen_inv hgen_ne word

  have hw_gen : (word.map gen).prod = 1 := by
    rw [← hφ_word]; exact hw_ker


  exact word_relation_trivial_in_coxeter_group gen hgen_inv hgen_ne hDel word hw_gen

end CoxeterSystemFromDeletion
