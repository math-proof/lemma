/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/GLnPanelExtension.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.Buildings.code.SphericalBuilding.GLnThinApartment
public import Structure.v1.Atlas.Buildings.code.SphericalBuilding.GLnPanelExtension

@[expose] public section

namespace GLnBuilding

variable (k : Type*) [Field k] (n : ℕ)


/-- Wrapper turning a `DirectPanelExtensionHyp` into a `PanelExtensionHyp`. -/
noncomputable def panelExtensionOfDirect
    (h : DirectPanelExtensionHyp k n) : PanelExtensionHyp k n where
  extend := h.extend

end GLnBuilding
