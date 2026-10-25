/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularDualPath.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopDisorderKacWard
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopCriticalWeight
import Instance.StatisticalMechanics.Code.Onsager.SignedLoopRectangularDualPath
open Finset SimpleGraph


namespace StatMech.Onsager

open StatMech.FrontierA StatMech.Sharpness

noncomputable section

def ons_rectDualGraph (M N : Nat) : SimpleGraph (ons_RectDualVertex M N) where
  Adj := ons_rectDualAdj M N
  symm := by
    constructor
    intro u v
    rintro (⟨hcoord, hdist⟩ | ⟨hcoord, hdist⟩)
    · exact Or.inl ⟨hcoord.symm, by simpa [Nat.dist_comm] using hdist⟩
    · exact Or.inr ⟨hcoord.symm, by simpa [Nat.dist_comm] using hdist⟩
  loopless := ⟨by
    intro u
    rintro (⟨_, hdist⟩ | ⟨_, hdist⟩) <;>
      simp at hdist⟩

end
end StatMech.Onsager
