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
import Structure.v1.Atlas.AlgebraicTopologyI.code.Lemma32_4
open Set Function


namespace OrientationTheorem

/-- Construction of the `RelativeHomologyColimitData` from a `CompactlySupportedDiagram`
on a decreasing sequence of compact closed subsets. The surjectivity and injectivity
conditions of the colimit are extracted from the compactly-supported data by combining
them with `compact_subset_complement_eventually`. This is the core lemma giving
$\varinjlim_i H_q(X, X - A_i) \cong H_q(X, X - A)$ in Lemma 32.4. -/
def RelativeHomologyColimitData.ofCompactDecreasing
    {X : Type*} [TopologicalSpace X]
    (A : ℕ → Set X)
    (_hA_compact : ∀ i, IsCompact (A i))
    (hA_closed : ∀ i, IsClosed (A i))
    (hA_decreasing : ∀ i, A (i + 1) ⊆ A i)
    (G : Set X → Type*) [∀ K, AddCommGroup (G K)]
    (csd : CompactlySupportedDiagram A G) :
    RelativeHomologyColimitData A G where
  ρ := csd.ρ
  φ := csd.φ
  compat := csd.compat
  surj := by
    intro x

    obtain ⟨K, hK_compact, hK_sub, hK_lift⟩ := csd.surj_support x

    obtain ⟨i, hKi⟩ := compact_subset_complement_eventually A hA_closed hA_decreasing K
      hK_compact hK_sub

    obtain ⟨g, hg⟩ := hK_lift i hKi
    exact ⟨i, g, hg⟩
  inj := by
    intro i g hg

    obtain ⟨K, hK_compact, hK_sub, hK_vanish⟩ := csd.inj_support i g hg

    obtain ⟨j, hKj⟩ := compact_subset_complement_eventually A hA_closed hA_decreasing K
      hK_compact hK_sub

    have hij : i ≤ max i j := le_max_left i j
    have hjmax : j ≤ max i j := le_max_right i j
    have hKmax : K ⊆ (A (max i j))ᶜ := hKj.trans
      (compl_subset_compl.mpr (antitone_nat_of_succ_le hA_decreasing hjmax))

    exact ⟨max i j, hij, hK_vanish (max i j) hij hKmax⟩

end OrientationTheorem
