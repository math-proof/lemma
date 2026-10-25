/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Lemma32_4.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.Section32.Part2
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section32
import Mathlib.Analysis.Convex.Contractible
open Set Function


namespace OrientationTheorem

/-- If `A i` is a decreasing sequence of closed sets and `K` is a compact set disjoint
from `⋂ i, A i`, then `K` is already disjoint from some `A i`. -/
lemma compact_subset_complement_eventually
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
