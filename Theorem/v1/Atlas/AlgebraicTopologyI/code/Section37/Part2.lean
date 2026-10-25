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
import Def.v1.Atlas.AlgebraicTopologyI.code.Section37.Part2
open CategoryTheory

open CategoryTheory TopologicalSpace Limits


namespace PoincareDuality

universe u

section OpenNhdsColimit

variable {α : Type u} [TopologicalSpace α]

namespace CombinedOpenNhds

variable {A : ℕ → Set α}

/-- The forgetful map `toNhdsInter` is monotone with respect to the reverse-inclusion
preorders. -/
theorem toNhdsInter_monotone (hA : Antitone A) :
    Monotone (toNhdsInter hA) := fun _ _ h => h

/-- Cofinality of `toNhdsInter`: in a Hausdorff space, every open neighbourhood of the
intersection $\bigcap_k A_k$ of an antitone family of compacts $A_k$ contains some $A_k$,
giving a refinement coming from a combined open neighbourhood. -/
theorem toNhdsInter_cofinal [T2Space α]
    (hA : Antitone A) (hcpt : ∀ k, IsCompact (A k)) :
    ∀ (V : OpenNhdsOfSet (⋂ k, A k)), ∃ (p : CombinedOpenNhds A),
      V ≤ toNhdsInter hA p := by
  intro V
  have hdir : Directed (· ⊇ ·) A :=
    fun i j => ⟨max i j, hA (le_max_left _ _), hA (le_max_right _ _)⟩
  obtain ⟨k, hk⟩ := exists_subset_nhds_of_isCompact hdir hcpt
    (fun x hx => V.toOpens.isOpen.mem_nhds (V.subset_carrier hx))
  exact ⟨⟨k, ⟨V.toOpens, hk⟩⟩, le_refl _⟩

/-- Finality of `toNhdsInter` as a functor: cofinality plus monotonicity in a Hausdorff
space ensure that colimits along the combined index agree with colimits along open
neighbourhoods of the intersection. -/
theorem toNhdsInter_functor_final [T2Space α]
    (hA : Antitone A) (hcpt : ∀ k, IsCompact (A k)) :
    letI : IsDirected (CombinedOpenNhds A) (· ≤ ·) := isDirectedOfAntitone hA
    (toNhdsInter_monotone hA).functor.Final := by
  letI : IsDirected (CombinedOpenNhds A) (· ≤ ·) := isDirectedOfAntitone hA
  rw [Monotone.final_functor_iff]
  exact toNhdsInter_cofinal hA hcpt

end CombinedOpenNhds
end OpenNhdsColimit
end PoincareDuality
