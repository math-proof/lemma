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
import Structure.v1.Atlas.AlgebraicTopologyI.code.Section37
open CategoryTheory

open CategoryTheory TopologicalSpace Limits


namespace PoincareDuality

universe u

section OpenNhdsColimit

variable {α : Type u} [TopologicalSpace α]

namespace OpenNhdsOfSet

variable {K : Set α}

/-- Reverse-inclusion preorder: $U \le V$ iff $V \subseteq U$, so that the system of
neighbourhoods is directed downward. -/
instance : Preorder (OpenNhdsOfSet K) where
  le U V := V.toOpens ≤ U.toOpens
  le_refl _ := le_refl _
  le_trans _ _ _ hab hbc := le_trans hbc hab

/-- $\alpha$ itself is always an open neighbourhood of $K$, so the type is nonempty. -/
instance : Nonempty (OpenNhdsOfSet K) := ⟨⟨⊤, Set.subset_univ K⟩⟩

/-- The preorder on open neighbourhoods is directed: any two neighbourhoods admit a common
refinement (their intersection). -/
instance : IsDirected (OpenNhdsOfSet K) (· ≤ ·) where
  directed U V :=
    ⟨⟨U.toOpens ⊓ V.toOpens,
      fun _ hx => ⟨U.subset_carrier hx, V.subset_carrier hx⟩⟩,
     (inf_le_left : U.toOpens ⊓ V.toOpens ≤ U.toOpens),
     (inf_le_right : U.toOpens ⊓ V.toOpens ≤ V.toOpens)⟩

end OpenNhdsOfSet
end OpenNhdsColimit
end PoincareDuality
