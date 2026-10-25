/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutInjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitCrossToggleMatching.Part8
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPairedCutHallExact
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitExactTagProjection
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPairedCutInjection.Part8
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

set_option maxHeartbeats 800000 in


theorem lpReplicaOrbitCanonicalLastTwoSlots_terminal
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : 2 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q)) :
    LPReplicaOrbitCommonSlotTerminal G sites q
      (lpReplicaOrbitCanonicalLastTwoSlots G sites q hcard) := by
  intro x hx y hxy
  letI : LinearOrder (LPReplicaOrbitCommonSlot G sites q) :=
    LinearOrder.lift' (lpReplicaOrbitCommonSlotOrderKey G sites q)
      (lpReplicaOrbitCommonSlotOrderKey_injective G sites q)
  let E := (Finset.univ : Finset
    (LPReplicaOrbitCommonSlot G sites q)).orderIsoOfFin Finset.card_univ
  have hxy' : x <= y := hxy
  let n := Fintype.card (LPReplicaOrbitCommonSlot G sites q)
  let a : Fin n := ⟨n - 2, by dsimp only [n]; omega⟩
  let b : Fin n := ⟨n - 1, by dsimp only [n]; omega⟩
  have hEa : (E a).1 =
      lpReplicaOrbitCanonicalPenultimateSlot G sites q hcard := by
    simp only [a, n, E, lpReplicaOrbitCanonicalPenultimateSlot]
    rfl
  have hEb : (E b).1 =
      lpReplicaOrbitCanonicalLastSlot G sites q hcard := by
    simp only [b, n, E, lpReplicaOrbitCanonicalLastSlot]
    rfl
  have hmem : x = lpReplicaOrbitCanonicalPenultimateSlot G sites q hcard ∨
      x = lpReplicaOrbitCanonicalLastSlot G sites q hcard := by
    simpa only [lpReplicaOrbitCanonicalLastTwoSlots, Finset.mem_insert,
      Finset.mem_singleton] using hx
  let iy := E.symm ⟨y, Finset.mem_univ y⟩
  have hEiy : (E iy).1 = y := by
    exact congrArg Subtype.val
      (E.apply_symm_apply ⟨y, Finset.mem_univ y⟩)
  have hiy : iy.val = n - 2 ∨ iy.val = n - 1 := by
    rcases hmem with hxpen | hxlast
    · have hindex : a <= iy := by
        apply E.le_iff_le.mp
        change (E a).1 <= (E iy).1
        rw [hEa, hEiy]
        simpa only [hxpen] using hxy'
      have hindexVal : a.val <= iy.val := hindex
      have hilt := iy.isLt
      dsimp only [a] at hindexVal
      dsimp only [n] at hilt ⊢
      omega
    · have hindex : b <= iy := by
        apply E.le_iff_le.mp
        change (E b).1 <= (E iy).1
        rw [hEb, hEiy]
        simpa only [hxlast] using hxy'
      have hindexVal : b.val <= iy.val := hindex
      have hilt := iy.isLt
      dsimp only [b] at hindexVal
      dsimp only [n] at hilt ⊢
      omega
  simp only [lpReplicaOrbitCanonicalLastTwoSlots, Finset.mem_insert,
    Finset.mem_singleton]
  rcases hiy with hiy | hiy
  · left
    have hiya : iy = a := Fin.ext hiy
    rw [<- hEa, <- hEiy, hiya]
  · right
    have hiyb : iy = b := Fin.ext hiy
    rw [<- hEb, <- hEiy, hiyb]


end
end StatMech.Ising
