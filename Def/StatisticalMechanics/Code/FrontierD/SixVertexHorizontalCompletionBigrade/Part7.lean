/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalCompletionBigrade.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCheckerHorizontalBigrade
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPairBigrade.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalCompletionBigrade.Part5
open Finset


namespace StatMech.FrontierD

noncomputable section

noncomputable def sigmaSubsingletonEquivSubtypeNonempty
    {A : Type*} (fiber : A -> Type*)
    [fiberSubsingleton : forall a, Subsingleton (fiber a)] :
    (Sigma fiber) ≃ {a : A // Nonempty (fiber a)} where
  toFun value := ⟨value.1, ⟨value.2⟩⟩
  invFun value := ⟨value.1, Classical.choice value.2⟩
  left_inv value := by
    rcases value with ⟨a, value⟩
    apply Sigma.ext
    · rfl
    · exact heq_of_eq
        (@Subsingleton.elim _ (fiberSubsingleton a) _ _)
  right_inv value := by
    apply Subtype.ext
    rfl


end
end StatMech.FrontierD
