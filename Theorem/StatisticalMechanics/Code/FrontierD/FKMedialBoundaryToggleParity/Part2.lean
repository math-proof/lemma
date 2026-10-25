/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialBoundaryToggleParity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryPermutation.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part2
open Equiv


namespace StatMech.FrontierD

variable {T : EvenTorus}


theorem card_fkMedialBlackDart (T : EvenTorus) :
    Fintype.card (FKMedialBlackDart T) = 2 * T.width * T.height := by
  rw [Fintype.card_congr (fkMedialBlackDartEquivVertexBool T)]
  simp [EvenTorus.Vertex]
  ring


theorem fkMedialBlackDart_eq_zero_or_one (d : FKMedialBlackDart T) :
    d = fkMedialBlackDart0 d.1.1 \/
      d = fkMedialBlackDart1 d.1.1 := by
  have h := (fkMedialBlackDartEquivVertexBool T).symm_apply_apply d
  change (if fkMedialBlackSideIndex d.1.2 then
      fkMedialBlackDart1 d.1.1 else fkMedialBlackDart0 d.1.1) = d at h
  cases hside : fkMedialBlackSideIndex d.1.2
  · exact Or.inl (by simpa [hside] using h.symm)
  · exact Or.inr (by simpa [hside] using h.symm)


end StatMech.FrontierD
