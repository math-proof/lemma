/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Link.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.Building.Labels
import Lemma.Finset.LabelMap.eq.ImageLabelMap.of.EqLabelMap_Head_ImageLabelMap_Head.IsChainAdjacent.Ne.All_EqLabelMap_ImageLabelMap
open scoped Classical

variable {V : Type*} [DecidableEq V]


namespace SimplicialComplex

/-- The *link complex* $\mathrm{lk}_K(\sigma)$ of a face $\sigma$ as a simplicial complex: its
faces are the nonempty $\tau$ disjoint from $\sigma$ such that $\sigma \cup \tau \in K$. -/
def linkComplex (K : SimplicialComplex V) (σ : Finset V)
    (hσ : σ ∈ K.faces) : SimplicialComplex V where
  faces := K.link σ hσ
  nonempty_of_mem := by
    intro s hs
    exact hs.1
  down_closed := by
    intro s t hs hts ht_ne

    obtain ⟨_, hsdisj, hsunion⟩ := hs
    refine ⟨ht_ne, ?_, ?_⟩
    ·
      exact Disjoint.mono_right hts hsdisj
    ·
      have h_sub : σ ∪ t ⊆ σ ∪ s := Finset.union_subset_union_right hts
      have h_ne : (σ ∪ t).Nonempty := by
        exact Finset.Nonempty.mono (Finset.subset_union_left) (K.nonempty_of_mem σ hσ)
      exact K.down_closed hsunion h_sub h_ne

end SimplicialComplex
