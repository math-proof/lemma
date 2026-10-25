/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/LocalityPrinciple.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.AlgebraicTopologyI.code.SubdivisionSmall.Part3
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.SubdivisionSmall
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section6
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section13
import Structure.v1.Atlas.AlgebraicTopologyI.code.Section6
import Def.v1.Atlas.AlgebraicTopologyI.code.Section13.Part3
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Def.v1.Atlas.AlgebraicTopologyI.code.LocalityPrinciple.Part2


noncomputable section

open CategoryTheory AlgebraicTopologyI Finset BigOperators BarycentricSubdivision

namespace LocalityPrinciple

variable (X : TopCat.{0}) (𝒜 : Set (Set X))

/-- The lift `singularChainsLift` intertwines the $k$-fold iterated subdivision
operator with the $k$-fold composite of the categorical subdivision operator. -/
lemma isSmallChain_mem_smallChainSubgroup {X : Type*} [TopologicalSpace X]
    (𝒜 : Set (Set X)) {n : ℕ} (c : SingularChains n X)
    (hc : IsSmallChain 𝒜 c) : c ∈ smallChainSubgroup n 𝒜 := by
  unfold smallChainSubgroup

  have hdecomp : (show FreeAbelianGroup (SingularSimplex n X) from c) =
      (FreeAbelianGroup.toFinsupp (show FreeAbelianGroup (SingularSimplex n X) from c)).sum
        (fun σ k => k • FreeAbelianGroup.of σ) := by
    conv_lhs => rw [← Finsupp.toFreeAbelianGroup_toFinsupp
      (show FreeAbelianGroup (SingularSimplex n X) from c)]
    simp [Finsupp.toFreeAbelianGroup, Finsupp.sum, Finsupp.liftAddHom_apply]
  change (show FreeAbelianGroup (SingularSimplex n X) from c) ∈ _
  rw [hdecomp]
  apply sum_mem
  intro σ hσ
  apply (AddSubgroup.closure _).zsmul_mem
  apply AddSubgroup.subset_closure
  exact ⟨σ, hc σ hσ, rfl⟩

end LocalityPrinciple
end
