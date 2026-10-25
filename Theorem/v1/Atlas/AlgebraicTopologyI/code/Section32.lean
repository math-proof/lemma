/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section32.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.Section30.Part4
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section30
import Mathlib.Topology.Basic
import Mathlib.Topology.Sets.Closeds
import Mathlib.Algebra.FiveLemma
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Structure.v1.Atlas.AlgebraicTopologyI.code.Section32.Part2
open Set Function


namespace OrientationTheorem

variable {M : Type*} [TopologicalSpace M]

/-- Companion to `compact_decreasing_sequence_subset_open` rephrased in
complement form: if `K` is a compact subset of the complement of
`⋂ i, A i` where `A i` is a decreasing sequence of closed sets, then
`K ⊆ (A i)ᶜ` already for some `i`. Proved using the directed-cover
formulation of compactness. -/
lemma compact_subset_complement_eventually_aux
    {X : Type*} [TopologicalSpace X]
    (A : ℕ → Set X) (hA_closed : ∀ i, IsClosed (A i))
    (hA_decreasing : ∀ i, A (i + 1) ⊆ A i)
    (K : Set X) (hK : IsCompact K)
    (hKA : K ⊆ (⋂ i, A i)ᶜ) :
    ∃ i, K ⊆ (A i)ᶜ := by
  rw [compl_iInter] at hKA
  exact hK.elim_directed_cover _ (fun i => (hA_closed i).isOpen_compl) hKA
    (Monotone.directed_le (fun i j hij =>
      compl_subset_compl.mpr (antitone_nat_of_succ_le hA_decreasing hij)))

end OrientationTheorem
