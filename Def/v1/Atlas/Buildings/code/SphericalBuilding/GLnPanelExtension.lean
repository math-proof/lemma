/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/GLnPanelExtension.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.SphericalBuilding.GLnThinApartment
import Structure.v1.Atlas.Buildings.code.SphericalBuilding.GLnPanelExtension


namespace GLnBuilding

variable (k : Type*) [Field k] (n : ℕ)


/-- Wrapper turning a `DirectPanelExtensionHyp` into a `PanelExtensionHyp`. -/
noncomputable def panelExtensionOfDirect
    (h : DirectPanelExtensionHyp k n) : PanelExtensionHyp k n where
  extend := h.extend

end GLnBuilding
