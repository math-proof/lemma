/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectFaithfulShearEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedDiagonalShearSubdivision.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectFaithfulShearEmbedding
open SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice

noncomputable section

theorem fkRectPairSite_injective : Function.Injective fkRectPairSite := by
  intro p q h
  apply Prod.ext
  · have := congrFun h 0
    simpa [fkRectPairSite] using this
  · have := congrFun h 1
    simpa [fkRectPairSite] using this

theorem fkRectFaithfulShearPair_injective :
    Function.Injective fkRectFaithfulShearPair := by
  rintro ⟨x, y⟩ ⟨a, b⟩ h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  simp [fkRectFaithfulShearPair] at hx hy
  apply Prod.ext <;> simp <;> omega

theorem fkRectFaithfulShearPoint_injective :
    Function.Injective fkRectFaithfulShearPoint := by
  intro p q h
  apply fkRectFaithfulShearPair_injective
  apply fkRectPairSite_injective
  exact h


end
end StatMech.FrontierD
