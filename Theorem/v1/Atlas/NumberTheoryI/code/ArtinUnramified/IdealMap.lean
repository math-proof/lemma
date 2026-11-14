/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Ideal.Maps


noncomputable section

namespace ArtinUnramified

section GaloisClassGroupAction

lemma ideal_map_comp_ringEquiv {R : Type*} [CommRing R]
    (e₁ e₂ : R ≃+* R) (I : Ideal R) :
    Ideal.map e₂ (Ideal.map e₁ I) = Ideal.map (e₁.trans e₂) I := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr; intro x hx
    obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective e₁ e₁.surjective).mp hx
    exact Ideal.mem_map_of_mem _ hy
  · apply Ideal.map_le_iff_le_comap.mpr; intro x hx
    exact Ideal.mem_map_of_mem e₂ (Ideal.mem_map_of_mem e₁ hx)

lemma ideal_map_refl_ringEquiv {R : Type*} [CommRing R] (I : Ideal R) :
    Ideal.map (RingEquiv.refl R) I = I := by
  apply le_antisymm
  · exact Ideal.map_le_iff_le_comap.mpr (fun x hx => by simpa using hx)
  · exact fun x hx => Ideal.mem_map_of_mem _ hx

end GaloisClassGroupAction
end ArtinUnramified
end
