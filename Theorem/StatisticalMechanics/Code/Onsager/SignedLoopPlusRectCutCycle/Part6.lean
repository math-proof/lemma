/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectCutCycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopAnchoredCutInjective
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopPlusWiredCut.Part5
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopPlusDualRectangle.Part4
import Theorem.StatisticalMechanics.Code.Ising.KWDualBijection.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.BoxGraphPath.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStar.Part4
import Theorem.StatisticalMechanics.Code.FK.EdgeConfigZ.Part15
import Def.StatisticalMechanics.Code.Onsager.SignedLoopPlusRectCutCycle.Part6
open Finset SimpleGraph
open scoped symmDiff


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.FrontierA StatMech.Walls

noncomputable section

theorem ons_rectHorizontalEdge_injective (M N : Nat) :
    Function.Injective
      (ons_rectHorizontalEdge : ons_RectHorizontalIndex M N ->
        Sym2 (ons_RectDualVertex M N)) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  rw [ons_rectHorizontalEdge, ons_rectHorizontalEdge, Sym2.eq_iff] at h
  rcases h with h | h
  · apply Prod.ext
    · apply Fin.ext
      exact congrArg (fun p : ons_RectDualVertex M N => p.1.val) h.1
    · exact congrArg (fun p : ons_RectDualVertex M N => p.2) h.1
  · have h1 : i.val = i'.val + 1 :=
      congrArg (fun p : ons_RectDualVertex M N => p.1.val) h.1
    have h2 : i.val + 1 = i'.val :=
      congrArg (fun p : ons_RectDualVertex M N => p.1.val) h.2
    omega

theorem ons_rectVerticalEdge_injective (M N : Nat) :
    Function.Injective
      (ons_rectVerticalEdge : ons_RectVerticalIndex M N ->
        Sym2 (ons_RectDualVertex M N)) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  rw [ons_rectVerticalEdge, ons_rectVerticalEdge, Sym2.eq_iff] at h
  rcases h with h | h
  · apply Prod.ext
    · exact congrArg (fun p : ons_RectDualVertex M N => p.1) h.1
    · apply Fin.ext
      exact congrArg (fun p : ons_RectDualVertex M N => p.2.val) h.1
  · have h1 : j.val = j'.val + 1 :=
      congrArg (fun p : ons_RectDualVertex M N => p.2.val) h.1
    have h2 : j.val + 1 = j'.val :=
      congrArg (fun p : ons_RectDualVertex M N => p.2.val) h.2
    omega

end
end StatMech.Onsager
