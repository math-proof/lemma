/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskAffineCycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamRowDataMaskHall.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamMaskAffineCycle
open Finset
open Classical


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem eq_of_middle_outer_colorClass_two_three
    (m : Finset I) (c d : ↑m -> Fin 4)
    (hmid : middleMask m c = middleMask m d)
    (hout : outerMask m c = outerMask m d)
    (htwo : colorClass m c 2 = colorClass m d 2)
    (hthree : colorClass m c 3 = colorClass m d 3) : c = d := by
  funext i
  have hmidMem := congrArg (fun S : Finset I => i.1 ∈ S) hmid
  have houtMem := congrArg (fun S : Finset I => i.1 ∈ S) hout
  have htwoMem := congrArg (fun S : Finset I => i.1 ∈ S) htwo
  have hthreeMem := congrArg (fun S : Finset I => i.1 ∈ S) hthree
  have hc : c i = 0 ∨ c i = 1 ∨ c i = 2 ∨ c i = 3 := by omega
  have hd : d i = 0 ∨ d i = 1 ∨ d i = 2 ∨ d i = 3 := by omega
  rcases hc with hc | hc | hc | hc <;>
    rcases hd with hd | hd | hd | hd <;>
    simp [middleMask, outerMask, mem_colorClass_iff, i.2, hc, hd] at *


end StatMech.GrahamGHS.FourColor
