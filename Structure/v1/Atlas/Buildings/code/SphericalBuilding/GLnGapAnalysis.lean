/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/GLnGapAnalysis.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.SphericalBuilding.GLnPanelExtension
import Theorem.v1.Atlas.Buildings.code.SphericalBuilding.GLnGapAnalysis


namespace GLnBuilding

variable (k : Type*) [Field k] (n : ℕ)


/-- Hypothesis: a panel (length $n-2$ chain) compatible with a frame can be extended to two
distinct chambers, both containing the panel. -/
structure PanelGapHyp where
  fill_gap : ∀ (F : Frame k n) (panel : SubspaceFlag k n),
    (∀ V ∈ panel.chain, F.IsCompatible k n V) →
    panel.chain.length = n - 2 →
    ∃ (chain₁ chain₂ : List (Submodule k (Vec k n))),
      chain₁ ≠ [] ∧
      chain₁.IsChain (· < ·) ∧
      (∀ V ∈ chain₁, V ≠ ⊥ ∧ V ≠ ⊤) ∧
      chain₁.length = n - 1 ∧
      chain₂ ≠ [] ∧
      chain₂.IsChain (· < ·) ∧
      (∀ V ∈ chain₂, V ≠ ⊥ ∧ V ≠ ⊤) ∧
      chain₂.length = n - 1 ∧
      (∀ V ∈ panel.chain, V ∈ chain₁) ∧
      (∀ V ∈ panel.chain, V ∈ chain₂) ∧
      chain₁ ≠ chain₂


/-- Hypothesis: given a panel and a compatible frame, one can produce two distinct subspaces
$W_1, W_2$ that, when inserted at a common position, each turn the panel into a chamber. -/
structure FrameGapFillerHyp where
  find_and_fill : ∀ (F : Frame k n) (panel : SubspaceFlag k n),
    (∀ V ∈ panel.chain, F.IsCompatible k n V) →
    panel.chain.length = n - 2 →
    ∃ (W₁ W₂ : Submodule k (Vec k n)) (pos : ℕ),
      W₁ ≠ W₂ ∧
      W₁ ≠ ⊥ ∧ W₁ ≠ ⊤ ∧
      W₂ ≠ ⊥ ∧ W₂ ≠ ⊤ ∧
      pos ≤ panel.chain.length ∧
      (panel.chain.insertIdx pos W₁).IsChain (· < ·) ∧
      (panel.chain.insertIdx pos W₁).length = n - 1 ∧
      (panel.chain.insertIdx pos W₂).IsChain (· < ·) ∧
      (panel.chain.insertIdx pos W₂).length = n - 1 ∧
      (∀ V ∈ panel.chain.insertIdx pos W₁, V ≠ ⊥ ∧ V ≠ ⊤) ∧
      (∀ V ∈ panel.chain.insertIdx pos W₂, V ≠ ⊥ ∧ V ≠ ⊤)


/-- Hypothesis: any length-$(n-2)$ chain admits two distinct frame-compatible insertions
$W_1, W_2$ at a common index, sandwiched strictly between the surrounding terms. -/
structure SubmoduleGapInsertionHyp where
  find_gap : ∀ (F : Frame k n) (chain : List (Submodule k (Vec k n))),
    chain.IsChain (· < ·) →
    (∀ V ∈ chain, F.IsCompatible k n V) →
    (∀ V ∈ chain, V ≠ ⊥ ∧ V ≠ ⊤) →
    chain.length = n - 2 →
    ∃ (W₁ W₂ : Submodule k (Vec k n)) (pos : ℕ),
      W₁ ≠ W₂ ∧
      W₁ ≠ ⊥ ∧ W₁ ≠ ⊤ ∧
      W₂ ≠ ⊥ ∧ W₂ ≠ ⊤ ∧
      pos ≤ chain.length ∧
      (∀ x ∈ chain.take pos, x < W₁) ∧
      (∀ y ∈ chain.drop pos, W₁ < y) ∧
      (∀ x ∈ chain.take pos, x < W₂) ∧
      (∀ y ∈ chain.drop pos, W₂ < y)

/-- Hypothesis bundling the bijective correspondence between $F$-compatible subspaces of
$k^n$ and subsets $S \subseteq \{1,\dots,n\}$ via $S \mapsto \bigoplus_{i \in S} L_i$; this
records the extraction, its inverse, strict-monotonicity, and properness preservation. -/
structure FrameFinsetCorrespondenceHyp where
  extract : Frame k n → Submodule k (Vec k n) → Finset (Fin n)
  extract_eq : ∀ (F : Frame k n) (V : Submodule k (Vec k n)),
    F.IsCompatible k n V →
    V = ⨆ i ∈ extract F V, F.lines i
  extract_ssubset : ∀ (F : Frame k n) (V₁ V₂ : Submodule k (Vec k n)),
    F.IsCompatible k n V₁ → F.IsCompatible k n V₂ →
    V₁ < V₂ → extract F V₁ ⊂ extract F V₂
  extract_nonempty : ∀ (F : Frame k n) (V : Submodule k (Vec k n)),
    F.IsCompatible k n V → V ≠ ⊥ → (extract F V).Nonempty
  extract_proper : ∀ (F : Frame k n) (V : Submodule k (Vec k n)),
    F.IsCompatible k n V → V ≠ ⊤ → extract F V ≠ Finset.univ
  lift_ssubset : ∀ (F : Frame k n) (S₁ S₂ : Finset (Fin n)),
    S₁ ⊂ S₂ → (⨆ i ∈ S₁, F.lines i) < (⨆ i ∈ S₂, F.lines i)
  lift_nonempty : ∀ (F : Frame k n) (S : Finset (Fin n)),
    S.Nonempty → (⨆ i ∈ S, F.lines i) ≠ ⊥
  lift_proper : ∀ (F : Frame k n) (S : Finset (Fin n)),
    S ≠ Finset.univ → (⨆ i ∈ S, F.lines i) ≠ ⊤
  lift_ne : ∀ (F : Frame k n) (S₁ S₂ : Finset (Fin n)),
    S₁ ≠ S₂ → (⨆ i ∈ S₁, F.lines i) ≠ (⨆ i ∈ S₂, F.lines i)

/-- Hypothesis: any strictly increasing chain of proper non-empty subsets of $\mathrm{Fin}\ n$
of length $n-2$ admits two distinct insertions at a common position. -/
structure FinsetChainGapHyp where
  find_gap : ∀ (chain : List (Finset (Fin n))),
    chain.IsChain (· ⊂ ·) →
    (∀ S ∈ chain, S.Nonempty) →
    (∀ S ∈ chain, S ≠ Finset.univ) →
    chain.length = n - 2 →
    ∃ (T₁ T₂ : Finset (Fin n)) (pos : ℕ),
      T₁ ≠ T₂ ∧
      T₁.Nonempty ∧ T₁ ≠ Finset.univ ∧
      T₂.Nonempty ∧ T₂ ≠ Finset.univ ∧
      pos ≤ chain.length ∧
      (∀ S ∈ chain.take pos, S ⊂ T₁) ∧
      (∀ S ∈ chain.drop pos, T₁ ⊂ S) ∧
      (∀ S ∈ chain.take pos, S ⊂ T₂) ∧
      (∀ S ∈ chain.drop pos, T₂ ⊂ S)

end GLnBuilding
