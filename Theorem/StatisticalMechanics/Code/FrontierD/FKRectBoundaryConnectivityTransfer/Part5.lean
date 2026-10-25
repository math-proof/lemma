/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusRandomCluster.Part5
import Theorem.StatisticalMechanics.Code.Foundations.FiniteNonnegativeMatrixRate.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part6
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


theorem fkRectLayerInputEmbed_injective {W : Nat} :
    Function.Injective (fkRectLayerInputEmbed :
      Bool × Fin W -> FKRectLayerVertex W) := by
  rintro ⟨b, x⟩ ⟨b', x'⟩ h
  cases b <;> cases b' <;> simp [fkRectLayerInputEmbed,
    fkRectLayerInitialRole, fkRectLayerOldRole] at h ⊢
  all_goals exact h

theorem fkRectLayerOutputEmbed_injective {W : Nat} :
    Function.Injective (fkRectLayerOutputEmbed :
      Bool × Fin W -> FKRectLayerVertex W) := by
  rintro ⟨b, x⟩ ⟨b', x'⟩ h
  cases b <;> cases b' <;> simp [fkRectLayerOutputEmbed,
    fkRectLayerInitialRole, fkRectLayerNewRole] at h ⊢
  all_goals exact h


end
end StatMech.FrontierD
