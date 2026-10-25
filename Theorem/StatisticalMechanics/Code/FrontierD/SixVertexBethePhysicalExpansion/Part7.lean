/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalExpansion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalReduction.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalExpansion.Part7
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexBetheWordCoefficient_eq_edgeBase_sub
    {n : Nat} (c : Real) (z : Fin (n + 1) -> Complex)
    (w : Finset (Fin (n + 1))) :
    sixVertexBetheWordCoefficient c z (Equiv.refl _) w =
      ∏ i, if i ∈ sixVertexBetheWordMLSet w then
        sixVertexBetheWordEdgeBase c z w i - 1
      else sixVertexBetheWordEdgeBase c z w i := by
  unfold sixVertexBetheWordCoefficient
  apply Finset.prod_congr rfl
  intro i _
  unfold sixVertexBetheWordEdgeFactor sixVertexBetheWordEdgeBase
  by_cases hi : i ∈ w
  · by_cases hn : finRotate (n + 1) i ∈ w
    · have hn' : i + 1 ∈ w := by simpa using hn
      simp [hi, hn']
    · have hn' : i + 1 ∉ w := by simpa using hn
      simp [hi, hn']
  · by_cases hn : finRotate (n + 1) i ∈ w
    · have hn' : i + 1 ∈ w := by simpa using hn
      simp [hi, hn']
    · have hn' : i + 1 ∉ w := by simpa using hn
      simp [hi, hn']

end
end StatMech.FrontierD
