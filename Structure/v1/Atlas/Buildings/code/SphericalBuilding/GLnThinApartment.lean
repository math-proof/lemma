/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/GLnThinApartment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.SphericalBuilding.GLnInstance


namespace GLnBuilding

variable (k : Type*) [Field k] (n : ℕ)

/-- Hypothesis: every panel (codimension-$1$ face of a chamber) of an apartment frame $F$ extends
in exactly two ways to a chamber, yielding the thin-apartment axiom for the $\mathrm{GL}_n$ building. -/
structure PanelExtensionHyp where
  extend : ∀ (F : Frame k n) (panel : SubspaceFlag k n),
    (∀ V ∈ panel.chain, F.IsCompatible k n V) →
    panel.chain.length = n - 2 →
    ∃ C₁ C₂ : SubspaceFlag k n,
      IsChamber k n C₁ ∧ IsChamber k n C₂ ∧ C₁ ≠ C₂ ∧
      (∀ V ∈ panel.chain, V ∈ C₁.chain) ∧
      (∀ V ∈ panel.chain, V ∈ C₂.chain)

end GLnBuilding
