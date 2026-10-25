/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part3
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section5
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section11
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.LocalityPrinciple
import Def.v1.Atlas.AlgebraicTopologyI.code.Section5.Part6
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section11
import Def.v1.Atlas.AlgebraicTopologyI.code.LocalityPrinciple.Part5
import Def.v1.Atlas.AlgebraicTopologyI.code.Section10.Part7
open CategoryTheory CategoryTheory.Limits AlgebraicTopologyI


namespace Excision

open AlgebraicTopology Set

noncomputable section

attribute [instance] subspaceChainInclusion_mono

set_option linter.unusedSectionVars false in
/-- The composition `secondIso_fwd ≫ secondIso_inv` is the identity. One half of the
isomorphism claim. -/
lemma secondIso_fwd_inv_id :
    secondIso_fwd φ ψ ≫ secondIso_inv φ ψ = 𝟙 _ := by
  apply (cancel_epi (cokernel.π (pullback.snd (f := φ) (g := ψ)))).mp
  simp only [secondIso_fwd, secondIso_inv, cokernel.π_desc_assoc, Category.comp_id]
  simp only [secondIso_imgToCokerPS, secondIso_coimToCokerPS, Category.assoc,
    ← Category.assoc (factorThruImage _), Abelian.factorThruImage_comp_coimageIsoImage'_inv,
    cokernel.π_desc]
  simp

set_option linter.unusedSectionVars false in
/-- The composition `secondIso_inv ≫ secondIso_fwd` is the identity. The other half of the
isomorphism claim. -/
lemma secondIso_inv_fwd_id :
    secondIso_inv φ ψ ≫ secondIso_fwd φ ψ = 𝟙 _ := by
  apply (cancel_epi (cokernel.π (biprod.inl ≫ factorThruImage (biprod.desc φ ψ)))).mp
  simp only [secondIso_inv, secondIso_fwd, cokernel.π_desc_assoc, Category.comp_id]
  apply (cancel_epi (factorThruImage (biprod.desc φ ψ))).mp
  simp only [secondIso_imgToCokerPS, secondIso_coimToCokerPS, Category.assoc,
    ← Category.assoc (factorThruImage _), Abelian.factorThruImage_comp_coimageIsoImage'_inv,
    cokernel.π_desc_assoc, cokernel.π_desc]


  have h_fst_zero : biprod.fst (X := 𝒜) (Y := ℬ) ≫ biprod.inl ≫ factorThruImage (biprod.desc φ ψ) ≫
    cokernel.π (biprod.inl ≫ factorThruImage (biprod.desc φ ψ)) = 0 := by
    have h : biprod.inl (X := 𝒜) (Y := ℬ) ≫ factorThruImage (biprod.desc φ ψ) ≫
      cokernel.π (biprod.inl ≫ factorThruImage (biprod.desc φ ψ)) = 0 := by
      rw [← Category.assoc]; exact cokernel.condition _
    simp only [h, comp_zero]
  have h_total := congr_arg (· ≫ factorThruImage (biprod.desc φ ψ) ≫
    cokernel.π (biprod.inl ≫ factorThruImage (biprod.desc φ ψ))) (biprod.total (X := 𝒜) (Y := ℬ))
  simp only [Preadditive.add_comp, Category.assoc, Category.id_comp] at h_total
  rw [h_fst_zero, zero_add] at h_total
  exact h_total

end
end Excision
