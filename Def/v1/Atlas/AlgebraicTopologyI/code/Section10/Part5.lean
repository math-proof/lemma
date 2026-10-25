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
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section10.Part2
open CategoryTheory CategoryTheory.Limits AlgebraicTopologyI


namespace Excision

open AlgebraicTopology Set

noncomputable section

/-- The defining short exact sequence of the relative chain complex
`0 → C_*(A) → C_*(X) → C_*(X, A) → 0`. -/
def bottomSES (X : Type) [TopologicalSpace X] (A : Set X) :
    ShortComplex (ChainComplex AddCommGrpCat ℕ) :=
  ShortComplex.mk (subspaceChainInclusion X A)
    (cokernel.π (subspaceChainInclusion X A))

/-- The short exact sequence with `A`-chains, small chains, and their cokernel:
`0 → C_*(A) → C^{\{A, B\}}_*(X) → C^{\{A, B\}}_*(X) / C_*(A) → 0`. Used to compare with
`bottomSES` via the excision SES morphism. -/
def topSES (X : Type) [TopologicalSpace X] (A B : Set X) :
    ShortComplex (ChainComplex AddCommGrpCat ℕ) :=
  ShortComplex.mk (smallChainInclusionA X A B)
    (cokernel.π (smallChainInclusionA X A B))

/-- The morphism of short exact sequences from `topSES X A B` (small chains) to
`bottomSES X A` (full chains), with identity on `C_*(A)`, the small inclusion on the middle
term, and the induced map on cokernels on the right. -/
def excisionSESMorphism (X : Type) [TopologicalSpace X] (A B : Set X) :
    topSES X A B ⟶ bottomSES X A :=
  ShortComplex.Hom.mk
    (τ₁ := 𝟙 _)
    (τ₂ := smallChainInclusion X A B)
    (τ₃ := cokernel.map (smallChainInclusionA X A B)
      (subspaceChainInclusion X A)
      (𝟙 _) (smallChainInclusion X A B)
      (by rw [Category.id_comp, smallChainInclusionA_comp_ι]))
    (comm₁₂ := by
      show 𝟙 _ ≫ subspaceChainInclusion X A =
        smallChainInclusionA X A B ≫ smallChainInclusion X A B
      rw [Category.id_comp, smallChainInclusionA_comp_ι])
    (comm₂₃ := by
      show smallChainInclusion X A B ≫ cokernel.π (subspaceChainInclusion X A) =
        cokernel.π (smallChainInclusionA X A B) ≫ cokernel.map _ _ (𝟙 _) _ _
      rw [cokernel.π_desc])

end
end Excision
