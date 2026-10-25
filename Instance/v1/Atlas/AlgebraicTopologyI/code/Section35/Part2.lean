/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section35.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.Section26.Part8
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section26
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section34
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section34.Part3
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Category.TopCat.Opens
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Colimit.Module
import Mathlib.Order.Cofinal
import Mathlib.Algebra.Exact
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Structure.v1.Atlas.AlgebraicTopologyI.code.Section35
open Set


namespace CechCohomology

open TopologicalSpace SingularCohomology CategoryTheory

variable {X : Type} [TopologicalSpace X]

/-- Preorder on relative neighborhood pairs: `p ≤ q` iff `q.U ⊆ p.U` and
`q.V ⊆ p.V` (smaller neighborhoods correspond to larger elements). -/
instance relNbhdPair_preorder {K L : Set X} : Preorder (RelNbhdPair K L) where
  le p q := q.U ≤ p.U ∧ q.V ≤ p.V
  le_refl _ := ⟨le_refl _, le_refl _⟩
  le_trans _ _ _ hpq hqr := ⟨le_trans hqr.1 hpq.1, le_trans hqr.2 hpq.2⟩

/-- The preorder of relative neighborhood pairs is directed: any two pairs
admit a common refinement obtained by intersecting their components. -/
instance relNbhdPair_directed {K L : Set X} :
    IsDirected (RelNbhdPair K L) (· ≤ ·) where
  directed p q := ⟨⟨p.U ⊓ q.U, p.V ⊓ q.V,
    fun _ hx => ⟨p.hK hx, q.hK hx⟩,
    fun _ hx => ⟨p.hL hx, q.hL hx⟩,
    inf_le_inf p.hVU q.hVU⟩,
    ⟨inf_le_left, inf_le_left⟩, ⟨inf_le_right, inf_le_right⟩⟩

/-- The preorder of relative neighborhood pairs is nonempty: the pair
`(⊤, ⊤)` (the whole space, the whole space) is always a valid neighborhood
pair. -/
instance relNbhdPair_nonempty {K L : Set X} : Nonempty (RelNbhdPair K L) :=
  ⟨⟨⊤, ⊤, fun _ _ => trivial, fun _ _ => trivial, le_refl _⟩⟩

end CechCohomology
