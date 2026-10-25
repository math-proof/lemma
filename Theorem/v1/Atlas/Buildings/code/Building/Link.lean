/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Link.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.Building.Labels
import Lemma.Finset.LabelMap.eq.ImageLabelMap.of.EqLabelMap_Head_ImageLabelMap_Head.IsChainAdjacent.Ne.All_EqLabelMap_ImageLabelMap
import Def.v1.Atlas.Buildings.code.Building.Link
open scoped Classical

variable {V : Type*} [DecidableEq V]


namespace SimplicialComplex

/-- Membership characterisation of $\mathrm{lk}_K(\sigma)$: $\tau$ lies in the link iff $\tau$ is
nonempty, disjoint from $\sigma$, and $\sigma \cup \tau$ is a face. -/
theorem mem_linkComplex_iff (K : SimplicialComplex V) (σ : Finset V)
    (hσ : σ ∈ K.faces) (τ : Finset V) :
    τ ∈ (K.linkComplex σ hσ).faces ↔
      τ.Nonempty ∧ Disjoint σ τ ∧ (σ ∪ τ) ∈ K.faces :=
  Iff.rfl

/-- For a face $w$ properly containing $\sigma$, the complement $w \setminus \sigma$ is a face of
$\mathrm{lk}_K(\sigma)$. -/
theorem mem_linkComplex_of_sdiff (K : SimplicialComplex V) (σ : Finset V)
    (hσ : σ ∈ K.faces) (w : Finset V) (hw : w ∈ K.faces) (hσw : σ ⊆ w)
    (hne : (w \ σ).Nonempty) :
    (w \ σ) ∈ (K.linkComplex σ hσ).faces := by
  rw [mem_linkComplex_iff]
  refine ⟨hne, ?_, ?_⟩
  · exact disjoint_sdiff_self_right
  · rw [Finset.union_sdiff_of_subset hσw]
    exact hw

end SimplicialComplex
