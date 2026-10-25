/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferGF2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferCoverageJoin.Part2
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem eq_of_rowClass_zero_of_fourColorMaskProfile_eq
    (m : Finset I) (c d : ↑m -> Fin 4)
    (hprofile : fourColorMaskProfile m c = fourColorMaskProfile m d)
    (hrow : rowClass m c 0 = rowClass m d 0) :
    c = d := by
  funext i
  have hmid := congrArg
    (fun S : Finset I × Finset I => i.1 ∈ S.1) hprofile
  have hout := congrArg
    (fun S : Finset I × Finset I => i.1 ∈ S.2) hprofile
  have hrow' := congrArg (fun S : Finset I => i.1 ∈ S) hrow
  have hc : c i = 0 ∨ c i = 1 ∨ c i = 2 ∨ c i = 3 := by omega
  have hd : d i = 0 ∨ d i = 1 ∨ d i = 2 ∨ d i = 3 := by omega
  rcases hc with hc | hc | hc | hc <;>
    rcases hd with hd | hd | hd | hd <;>
    simp [fourColorMaskProfile, middleMask, outerMask, rowClass,
      mem_colorClass_iff, i.2, hc, hd] at hmid hout hrow' ⊢


end StatMech.GrahamGHS.FourColor
