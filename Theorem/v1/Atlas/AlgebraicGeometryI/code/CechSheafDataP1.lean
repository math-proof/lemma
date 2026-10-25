/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CechSheafDataP1.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.AlgebraicGeometryI.code.CechCohomologyIdentification
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CechCohomologyIdentification
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.GenusConstruction
import Def.v1.Atlas.AlgebraicGeometryI.code.GenusConstruction.Part2
import Instance.v1.Atlas.AlgebraicGeometryI.code.CechSheafDataP1


noncomputable section

universe v

namespace CechSheafDataP1

open SerreDualityTate CanonicalSheafCurves GenusConstruction

open TateCechInfra

variable (k : Type) [Field k]


/-- For the standard two-open cover of `P¹`, the first Čech cohomology of the structure sheaf
vanishes. -/
lemma finrank_cechH1_eq_zero :
    Module.finrank k (tateSetupP1 k).cechH1 = 0 := by

  show Module.finrank k ((tateSetupP1 k).V ⧸ ((tateSetupP1 k).V₁ ⊔ (tateSetupP1 k).V₂)) = 0
  have h_top : (tateSetupP1 k).V₁ ⊔ (tateSetupP1 k).V₂ = ⊤ := by
    show (⊤ : Submodule k k) ⊔ ⊤ = ⊤
    exact sup_idem _
  rw [h_top]

  show Module.finrank k (k ⧸ (⊤ : Submodule k k)) = 0
  have h := Submodule.finrank_quotient_add_finrank (⊤ : Submodule k k)
  rw [finrank_top k k] at h
  omega

/-- For the standard cover of `P¹`, the 0-th Čech cohomology of the dual setup also vanishes. -/
lemma finrank_dual_cechH0_eq_zero :
    Module.finrank k ↥(tateSetupP1 k).dual.cechH0 = 0 := by

  unfold tateSetupP1 TateDualitySetup.dual TateDualitySetup.cechH0
  simp only

  have h_top_ann : (⊤ : Submodule k k).dualAnnihilator = ⊥ :=
    Submodule.dualAnnihilator_top
  rw [h_top_ann]
  simp


end CechSheafDataP1
end
