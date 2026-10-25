/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/GLnInstance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.SphericalBuilding.GLn.Part3
import Lemma.Nat.TypeA_CoxeterMatrixA
import Structure.v1.Atlas.Buildings.code.SphericalBuilding.GLnInstance


namespace GLnBuilding

variable (k : Type*) [Field k] (n : ℕ)


/-- Assembling the three hypotheses (thin apartments, common apartment, apartment iso)
into the building structure for $\mathrm{GL}_n(k)$. -/
noncomputable def glnIsBuilding
    (h_thin : ThinApartmentHyp k n)
    (h_common : CommonApartmentHyp k n)
    (h_iso : ApartmentIsoHyp k n) : IsBuilding k n where
  apartment_thin := h_thin.extend_panel
  common_apartment := h_common.refine_flags
  apartment_iso := h_iso.iso_apartments

end GLnBuilding
