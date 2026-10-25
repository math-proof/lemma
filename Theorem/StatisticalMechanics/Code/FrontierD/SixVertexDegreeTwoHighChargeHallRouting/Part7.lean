/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeHallRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents.Part31
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexActiveKeyComponentRouting.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeHallRouting.Part8
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem SixVertexHorizontalDegreeTwoHighChargeHallRouting.reconnect_supported
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (routing : SixVertexHorizontalDegreeTwoHighChargeHallRouting T middle
      hmiddle_pos hmiddle_lt grade) (source) :
    sixVertexHorizontalOffDiagonalTwoCycleSupport T middle
      hmiddle_pos hmiddle_lt grade source (routing.reconnect source) := by
  by_cases hhigh : sixVertexHorizontalDegreeTwoHighCharge source
  · rw [SixVertexHorizontalDegreeTwoHighChargeHallRouting.reconnect,
      dif_pos hhigh]
    rcases routing.pairedMatching_related ⟨source, hhigh⟩ with
      ⟨branch, hbranch⟩
    rw [← hbranch]
    exact routing.paired_supported ⟨source, hhigh⟩ branch
  · rw [SixVertexHorizontalDegreeTwoHighChargeHallRouting.reconnect,
      dif_neg hhigh]
    exact routing.direct_supported ⟨source, hhigh⟩

theorem SixVertexHorizontalDegreeTwoHighChargeHallRouting.reconnect_injective
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (routing : SixVertexHorizontalDegreeTwoHighChargeHallRouting T middle
      hmiddle_pos hmiddle_lt grade) :
    Function.Injective routing.reconnect := by
  intro first second heq
  by_cases hfirst : sixVertexHorizontalDegreeTwoHighCharge first <;>
    by_cases hsecond : sixVertexHorizontalDegreeTwoHighCharge second
  · have hp : routing.pairedMatching ⟨first, hfirst⟩ =
        routing.pairedMatching ⟨second, hsecond⟩ := by
      simpa [SixVertexHorizontalDegreeTwoHighChargeHallRouting.reconnect,
        hfirst, hsecond] using heq
    exact congrArg Subtype.val (routing.pairedMatching_injective hp)
  · rcases routing.pairedMatching_related ⟨first, hfirst⟩ with
      ⟨branch, hbranch⟩
    exfalso
    apply routing.direct_paired_disjoint ⟨second, hsecond⟩
      ⟨first, hfirst⟩ branch
    calc
      routing.direct ⟨second, hsecond⟩ = routing.reconnect second := by
        simp [SixVertexHorizontalDegreeTwoHighChargeHallRouting.reconnect,
          hsecond]
      _ = routing.reconnect first := heq.symm
      _ = routing.pairedMatching ⟨first, hfirst⟩ := by
        simp [SixVertexHorizontalDegreeTwoHighChargeHallRouting.reconnect,
          hfirst]
      _ = routing.paired ⟨first, hfirst⟩ branch := hbranch.symm
  · rcases routing.pairedMatching_related ⟨second, hsecond⟩ with
      ⟨branch, hbranch⟩
    exfalso
    apply routing.direct_paired_disjoint ⟨first, hfirst⟩
      ⟨second, hsecond⟩ branch
    calc
      routing.direct ⟨first, hfirst⟩ = routing.reconnect first := by
        simp [SixVertexHorizontalDegreeTwoHighChargeHallRouting.reconnect,
          hfirst]
      _ = routing.reconnect second := heq
      _ = routing.pairedMatching ⟨second, hsecond⟩ := by
        simp [SixVertexHorizontalDegreeTwoHighChargeHallRouting.reconnect,
          hsecond]
      _ = routing.paired ⟨second, hsecond⟩ branch := hbranch.symm
  · have hd : routing.direct ⟨first, hfirst⟩ =
        routing.direct ⟨second, hsecond⟩ := by
      simpa [SixVertexHorizontalDegreeTwoHighChargeHallRouting.reconnect,
        hfirst, hsecond] using heq
    exact congrArg Subtype.val (routing.direct_injective hd)


end
end StatMech.FrontierD
