/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/GLnThinApartment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.SphericalBuilding.GLnInstance
import Structure.v1.Atlas.Buildings.code.SphericalBuilding.GLnThinApartment


namespace GLnBuilding

variable (k : Type*) [Field k] (n : ℕ)

/-- Converts a `PanelExtensionHyp` into the bundled `ThinApartmentHyp` consumed by the building
construction. -/
noncomputable def thinApartmentHyp
    (h : PanelExtensionHyp k n) : ThinApartmentHyp k n where
  extend_panel := fun F panel hcompat hlen => by
    obtain ⟨C₁, C₂, hch1, hch2, hne, hmem1, hmem2⟩ := h.extend F panel hcompat hlen
    exact ⟨C₁, C₂, hch1, hch2, hne, hmem1, hmem2, fun V hV => ⟨hmem1 V hV, hmem2 V hV⟩⟩

end GLnBuilding
