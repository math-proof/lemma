/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/FundamentalThm.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Theorem.v1.Atlas.AlgebraicTopologyI.code.FundamentalThm


noncomputable section

open CategoryTheory Category Limits ChainComplex HomologicalComplex

universe v u

namespace FundamentalThm

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace Resolution

variable {Z : C}

/-- The cokernel cofork on `d : E₁ ⟶ E₀` given by the augmentation `π : E₀ ⟶ Z`. -/
noncomputable def cokernelCofork (Q : Resolution Z) :
    CokernelCofork (Q.complex.d 1 0) :=
  CokernelCofork.ofπ _ Q.complex_d_comp_π_f_zero

/-- The augmentation `π : E₀ ⟶ Z` exhibits `Z` as the cokernel of `d : E₁ ⟶ E₀`, since the
underlying complex is exact in degree zero as a consequence of `π` being a quasi-isomorphism. -/
noncomputable def isColimitCokernelCofork (Q : Resolution Z) :
    IsColimit Q.cokernelCofork := by
  refine IsColimit.ofIsoColimit (Q.complex.opcyclesIsCokernel 1 0 (by simp)) ?_
  refine Cofork.ext (Q.complex.isoHomologyι₀.symm ≪≫ isoOfQuasiIsoAt Q.π 0 ≪≫
    singleObjHomologySelfIso _ _ _) ?_
  rw [← cancel_mono (singleObjHomologySelfIso (ComplexShape.down ℕ) 0 _).inv,
    ← cancel_mono (isoHomologyι₀ _).hom]
  dsimp [cokernelCofork]
  simp only [isoHomologyι₀_inv_naturality_assoc, p_opcyclesMap_assoc, single₀_obj_zero, assoc,
    Iso.hom_inv_id, comp_id, isoHomologyι_inv_hom_id, singleObjHomologySelfIso_inv_homologyι,
    singleObjOpcyclesSelfIso_hom, single₀ObjXSelf, Iso.refl_inv, id_comp]

end Resolution
end FundamentalThm
end
