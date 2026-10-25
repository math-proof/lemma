/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section37.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Topology.Compactness.Compact
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Category.TopCat.Opens
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Comma.Final
import Mathlib.Topology.Separation.Hausdorff
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section34.Part3
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section34
import Instance.v1.Atlas.AlgebraicTopologyI.code.Section37.Part2
open CategoryTheory

open CategoryTheory TopologicalSpace Limits


namespace PoincareDuality

universe u

section OpenNhdsColimit

variable {α : Type u} [TopologicalSpace α]

namespace CombinedOpenNhds

variable {A : ℕ → Set α}

/-- For an antitone (decreasing) family of subsets $A_k$, the preorder on combined
neighbourhoods is directed: take a common refinement index and intersect the neighbourhoods. -/
@[reducible]
def isDirectedOfAntitone (hA : Antitone A) :
    IsDirected (CombinedOpenNhds A) (· ≤ ·) where
  directed p q :=
    ⟨⟨max p.idx q.idx,
      ⟨p.nhd.toOpens ⊓ q.nhd.toOpens,
       fun _ hx => ⟨p.nhd.subset_carrier (hA (le_max_left _ _) hx),
                     q.nhd.subset_carrier (hA (le_max_right _ _) hx)⟩⟩⟩,
     (inf_le_left : p.nhd.toOpens ⊓ q.nhd.toOpens ≤ p.nhd.toOpens),
     (inf_le_right : p.nhd.toOpens ⊓ q.nhd.toOpens ≤ q.nhd.toOpens)⟩

/-- Forgetful map from a combined open neighbourhood $(k, U)$ to an open neighbourhood of
the intersection $\bigcap_k A_k$: since $\bigcap_k A_k \subseteq A_k \subseteq U$. -/
def toNhdsInter (_hA : Antitone A) :
    CombinedOpenNhds A → OpenNhdsOfSet (⋂ k, A k) :=
  fun p => ⟨p.nhd.toOpens, Set.iInter_subset_of_subset p.idx p.nhd.subset_carrier⟩

end CombinedOpenNhds
end OpenNhdsColimit
end PoincareDuality
