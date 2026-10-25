/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorUniformMaskSelector.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorAdmissibleRepair.Part4
import Def.StatisticalMechanics.Code.FrontierA.GrahamFourColorUniformMaskSelector.Part3
open Finset
open Classical


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {ι W : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype W] [DecidableEq W]


theorem leftMaskReference_spec
    (ends : ι -> Sym2 W) (m : Finset ι) (j k l zero : W)
    (p : Finset ι × Finset ι)
    (h : ∃ c : ↑m -> Fin 4,
      LeftPattern ends m {j, k} {k, l} k zero c ∧
        fourColorMaskProfile m c = p) :
    LeftPattern ends m {j, k} {k, l} k zero
        (leftMaskReference ends m j k l zero p) ∧
      fourColorMaskProfile m (leftMaskReference ends m j k l zero p) = p := by
  have h' : ∃ c : ↑m -> Fin 4,
      IsLeftMaskCandidate ends m j k l zero p c := h
  rw [leftMaskReference, dif_pos h']
  exact (Classical.choose_spec
    (exists_minimal_leftMaskCandidate ends m j k l zero p h')).1

theorem leftMaskReference_minimal
    (ends : ι -> Sym2 W) (m : Finset ι) (j k l zero : W)
    (p : Finset ι × Finset ι)
    (h : ∃ c : ↑m -> Fin 4,
      LeftPattern ends m {j, k} {k, l} k zero c ∧
        fourColorMaskProfile m c = p)
    (d : ↑m -> Fin 4)
    (hd : LeftPattern ends m {j, k} {k, l} k zero d)
    (hdp : fourColorMaskProfile m d = p) :
    canonicalTransferSize ends m k zero
        (leftMaskReference ends m j k l zero p) <=
      canonicalTransferSize ends m k zero d := by
  have h' : ∃ c : ↑m -> Fin 4,
      IsLeftMaskCandidate ends m j k l zero p c := h
  rw [leftMaskReference, dif_pos h']
  exact (Classical.choose_spec
    (exists_minimal_leftMaskCandidate ends m j k l zero p h')).2 d ⟨hd, hdp⟩

@[simp] theorem fourColorMaskProfile_balancedSwap
    (m X Y : Finset ι) (c : ↑m -> Fin 4) :
    fourColorMaskProfile m (balancedSwap m X Y c) =
      fourColorMaskProfile m c := by
  simp [fourColorMaskProfile, middleMask_balancedSwap,
    outerMask_balancedSwap]


end StatMech.GrahamGHS.FourColor
