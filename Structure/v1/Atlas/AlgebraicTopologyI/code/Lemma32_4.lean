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
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Lemma32_4
open Set Function


namespace OrientationTheorem

/-- Data packaging "compactly supported" surjectivity and injectivity hypotheses for the
sequence of groups `G (A i)` mapping to `G (⋂ A i)`. Each element of the limit group is
represented modulo a compact support condition, and each kernel element vanishes after
restricting to a compact support. This is the abstract input to the colimit step of the
proof of Lemma 32.4. -/
structure CompactlySupportedDiagram {X : Type*} [TopologicalSpace X]
    (A : ℕ → Set X)
    (G : Set X → Type*)
    [∀ K, AddCommGroup (G K)] where
  ρ : ∀ i, G (A i) →+ G (⋂ j, A j)
  φ : ∀ (i j : ℕ), i ≤ j → G (A i) →+ G (A j)
  compat : ∀ i j (hij : i ≤ j), (ρ j).comp (φ i j hij) = ρ i
  surj_support : ∀ (x : G (⋂ j, A j)),
    ∃ (K : Set X), IsCompact K ∧ K ⊆ (⋂ i, A i)ᶜ ∧
      ∀ i, K ⊆ (A i)ᶜ → ∃ g : G (A i), ρ i g = x
  inj_support : ∀ (i : ℕ) (g : G (A i)), ρ i g = 0 →
    ∃ (K : Set X), IsCompact K ∧ K ⊆ (⋂ n, A n)ᶜ ∧
      ∀ j (hij : i ≤ j), K ⊆ (A j)ᶜ → φ i j hij g = 0

end OrientationTheorem
