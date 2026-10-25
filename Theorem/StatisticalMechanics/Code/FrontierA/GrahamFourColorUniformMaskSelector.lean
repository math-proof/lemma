/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorUniformMaskSelector.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorAdmissibleRepair.Part4
import Def.StatisticalMechanics.Code.FrontierA.GrahamFourColorUniformMaskSelector
open Finset
open Classical


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {ι W : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype W] [DecidableEq W]


theorem middleMask_disjoint_outerMask (m : Finset ι) (c : ↑m -> Fin 4) :
    Disjoint (middleMask m c) (outerMask m c) := by
  rw [Finset.disjoint_left]
  intro i hiM hiO
  rcases Finset.mem_union.mp hiM with hi1 | hi2 <;>
    rcases Finset.mem_union.mp hiO with hi0 | hi3
  · exact (Finset.disjoint_left.mp
      (colorClass_disjoint m c (show (1 : Fin 4) ≠ 0 by decide))) hi1 hi0
  · exact (Finset.disjoint_left.mp
      (colorClass_disjoint m c (show (1 : Fin 4) ≠ 3 by decide))) hi1 hi3
  · exact (Finset.disjoint_left.mp
      (colorClass_disjoint m c (show (2 : Fin 4) ≠ 0 by decide))) hi2 hi0
  · exact (Finset.disjoint_left.mp
      (colorClass_disjoint m c (show (2 : Fin 4) ≠ 3 by decide))) hi2 hi3

theorem canonicalTransferSize_eq_card_union
    {ends : ι -> Sym2 W} {m : Finset ι} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {c : ↑m -> Fin 4}
    (hc : LeftPattern ends m {j, k} {k, l} k zero c) :
    canonicalTransferSize ends m k zero c =
      #(canonicalTransferUnion ends m k zero c) := by
  have hv := canonicalTransfers_valid hloop hjk hkl hc
  have hdisj : Disjoint
      (canonicalMiddleTransfer ends m c k zero)
      (canonicalOuterTransfer ends m c k zero) :=
    (middleMask_disjoint_outerMask m c).mono hv.1 hv.2.1
  unfold canonicalTransferSize canonicalTransferUnion
  rw [Finset.card_union_of_disjoint hdisj]

end StatMech.GrahamGHS.FourColor
