/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalCFT.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.NumberTheoryI.code.LocalCFT
open scoped RestrictedProduct
open Filter Set


noncomputable section

open scoped Pointwise

structure LocalArtinReciprocity where
  Kx : Type*
  [kx_comm_group : CommGroup Kx]
  [kx_topological_space : TopologicalSpace Kx]
  [kx_topological_group : IsTopologicalGroup Kx]
  I : Type*
  [ext_preorder : PartialOrder I]
  GalLK : I → Type*
  [gal_comm_group : ∀ i, CommGroup (GalLK i)]
  [gal_fintype : ∀ i, Fintype (GalLK i)]
  normGroup : I → Subgroup Kx
  artinMap : ∀ i, Kx →* GalLK i
  artinMap_surjective : ∀ i, Function.Surjective (artinMap i)
  artinMap_ker : ∀ i, (artinMap i).ker = normGroup i
  restrictMap : ∀ {i j : I}, i ≤ j → GalLK j →* GalLK i
  artinMap_compat : ∀ {i j : I} (h : i ≤ j) (x : Kx),
    restrictMap h (artinMap j x) = artinMap i x
  normGroup_antitone : ∀ {i j : I}, i ≤ j → normGroup j ≤ normGroup i
  normGroup_reflects_le : ∀ {i j : I}, normGroup j ≤ normGroup i → i ≤ j
  exists_sup : ∀ (i j : I), ∃ k : I, i ≤ k ∧ j ≤ k ∧
    normGroup k = normGroup i ⊓ normGroup j
  exists_inf : ∀ (i j : I), ∃ k : I, k ≤ i ∧ k ≤ j ∧
    normGroup k = normGroup i ⊔ normGroup j
  normGroup_isClosed : ∀ i, IsClosed (normGroup i : Set Kx)
  galois_subext : ∀ (i : I) (S : Subgroup (GalLK i)),
    ∃ j : I, j ≤ i ∧ normGroup j = S.comap (artinMap i)
  J : Type*
  unramifiedEmb : J → I
  frobElt : ∀ (j : J), GalLK (unramifiedEmb j)
  IsUniformizer : Kx → Prop
  artinMap_uniformizer_eq_frob : ∀ (j : J) (π : Kx),
    IsUniformizer π → artinMap (unramifiedEmb j) π = frobElt j

end
