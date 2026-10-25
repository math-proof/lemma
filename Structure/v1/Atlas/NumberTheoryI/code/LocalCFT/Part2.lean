/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalCFT.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Class.v1.Atlas.NumberTheoryI.code.LocalCFT
open scoped RestrictedProduct
open Filter Set


noncomputable section

open scoped Pointwise

attribute [instance] LocalArtinReciprocity.kx_comm_group
  LocalArtinReciprocity.kx_topological_space
  LocalArtinReciprocity.kx_topological_group
  LocalArtinReciprocity.ext_preorder
  LocalArtinReciprocity.gal_comm_group
  LocalArtinReciprocity.gal_fintype

namespace LocalArtinReciprocity

variable (D : LocalArtinReciprocity)

structure LocalArtinMap extends LocalArtinReciprocity where
  GalAb : Type*
  [galAb_group : CommGroup GalAb]
  [galAb_topological_space : TopologicalSpace GalAb]
  [galAb_topological_group : IsTopologicalGroup GalAb]
  [galAb_compact : CompactSpace GalAb]
  [gal_topological_space : ∀ i, TopologicalSpace (GalLK i)]
  [gal_discrete_topology : ∀ i, DiscreteTopology (GalLK i)]
  artinHom : Kx →* GalAb
  artinHom_continuous : Continuous artinHom
  proj : ∀ i, GalAb →* GalLK i
  proj_continuous : ∀ i, Continuous (proj i)
  artinMap_eq_proj : ∀ i x, artinMap i x = proj i (artinHom x)
  proj_jointly_injective : ∀ g : GalAb, (∀ i, proj i g = 1) → g = 1
  proj_compat : ∀ {i j : I} (h : i ≤ j) (g : GalAb),
    restrictMap h (proj j g) = proj i g
  proj_nhd_basis : ∀ (g : GalAb) (U : Set GalAb), U ∈ nhds g →
    ∃ i, {h : GalAb | proj i h = proj i g} ⊆ U

end LocalArtinReciprocity
end
