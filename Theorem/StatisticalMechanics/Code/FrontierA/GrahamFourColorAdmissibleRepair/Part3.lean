/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorAdmissibleRepair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorInvariantMasks
import Def.StatisticalMechanics.Code.FrontierA.GrahamFourColorAdmissibleRepair.Part3
open Finset
open Classical
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {ι W : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype W] [DecidableEq W]


@[simp] theorem subtype_mem_colorClass_iff
    (m : Finset ι) (c : ↑m -> Fin 4) (i : ↑m) (a : Fin 4) :
    (i : ι) ∈ colorClass m c a ↔ c i = a := by
  rw [mem_colorClass_iff]
  constructor
  · rintro ⟨hi, hci⟩
    have heq : (⟨i, hi⟩ : ↑m) = i := Subtype.ext rfl
    simpa only [heq] using hci
  · intro hci
    exact ⟨i.2, hci⟩


theorem balancedSwap_difference
    (m : Finset ι) (c d : ↑m -> Fin 4)
    (hmid : middleMask m c = middleMask m d)
    (hout : outerMask m c = outerMask m d) :
    balancedSwap m (balancedMiddleDifference m c d)
      (balancedOuterDifference m c d) c = d := by
  funext i
  have hi : (i : ι) ∈ m := i.2
  have hmidi : (i : ι) ∈ middleMask m c ↔ (i : ι) ∈ middleMask m d := by
    rw [hmid]
  have houti : (i : ι) ∈ outerMask m c ↔ (i : ι) ∈ outerMask m d := by
    rw [hout]
  have hmidi' : (c i = 1 ∨ c i = 2) ↔ (d i = 1 ∨ d i = 2) := by
    simpa [middleMask] using hmidi
  have houti' : (c i = 0 ∨ c i = 3) ↔ (d i = 0 ∨ d i = 3) := by
    simpa [outerMask] using houti
  have hc : c i = 0 ∨ c i = 1 ∨ c i = 2 ∨ c i = 3 := by omega
  have hd : d i = 0 ∨ d i = 1 ∨ d i = 2 ∨ d i = 3 := by omega
  rcases hc with hc | hc | hc | hc <;>
    rcases hd with hd | hd | hd | hd <;>
      simp [balancedMiddleDifference, balancedOuterDifference,
        Finset.mem_symmDiff, balancedSwap, middleSwapOn, outerSwapOn,
        Equiv.swap_apply_def, hc, hd] at hmidi' houti' ⊢

theorem balancedMiddleDifference_subset
    (m : Finset ι) (c d : ↑m -> Fin 4)
    (hmid : middleMask m c = middleMask m d) :
    balancedMiddleDifference m c d ⊆ middleMask m c := by
  intro i hi
  rw [balancedMiddleDifference, Finset.mem_symmDiff] at hi
  rcases hi with hi | hi
  · exact Finset.mem_union_left _ hi.1
  · rw [hmid]
    exact Finset.mem_union_left _ hi.1

theorem balancedOuterDifference_subset
    (m : Finset ι) (c d : ↑m -> Fin 4)
    (hout : outerMask m c = outerMask m d) :
    balancedOuterDifference m c d ⊆ outerMask m c := by
  intro i hi
  rw [balancedOuterDifference, Finset.mem_symmDiff] at hi
  rcases hi with hi | hi
  · exact Finset.mem_union_left _ hi.1
  · rw [hout]
    exact Finset.mem_union_left _ hi.1


theorem left_right_sameMasks_admissible
    {ends : ι -> Sym2 W} {m : Finset ι} {j k l zero : W}
    {c d : ↑m -> Fin 4}
    (hc : LeftPattern ends m {j, k} {k, l} k zero c)
    (hd : RightPattern ends m {j, k} {k, l} k zero d)
    (hmid : middleMask m c = middleMask m d)
    (hout : outerMask m c = outerMask m d) :
    let X := balancedMiddleDifference m c d
    let Y := balancedOuterDifference m c d
    X ⊆ middleMask m c ∧
      Y ⊆ outerMask m c ∧
      sources ends X = {k, l} ∧
      sources ends Y = ∅ ∧
      BalancedRepairAdmissible ends m X k zero c Y ∧
      balancedSwap m X Y c = d := by
  dsimp only
  have hX := balancedMiddleDifference_subset m c d hmid
  have hY := balancedOuterDifference_subset m c d hout
  have hsrcX : sources ends (balancedMiddleDifference m c d) = {k, l} := by
    rw [balancedMiddleDifference, sources_symmDiff, hc.2.1, hd.2.1]
    simp
  have hsrcY : sources ends (balancedOuterDifference m c d) = ∅ := by
    rw [balancedOuterDifference, sources_symmDiff, hc.1, hd.1]
    exact symmDiff_self ({j, k} : Finset W)
  have hswap := balancedSwap_difference m c d hmid hout
  refine ⟨hX, hY, hsrcX, hsrcY, ?_, hswap⟩
  refine ⟨hY, hsrcY, hc.2.2.2.2, ?_⟩
  rw [hswap]
  exact hd.2.2.2.2


end StatMech.GrahamGHS.FourColor
