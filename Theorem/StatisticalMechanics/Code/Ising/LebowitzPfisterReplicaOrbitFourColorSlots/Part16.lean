/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorRecovery
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitOrientedFourColor.Part3
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorSlots.Part16
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

@[simp] theorem lpReplicaOrbitFourColorSlotRecolor_allocation
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (X Y : Finset (LPReplicaOrbitCommonSlot G sites q))
    (s : LPReplicaOrbitFourColorSlotState G sites q) :
    (lpReplicaOrbitFourColorSlotRecolor G sites q X Y s).allocation =
      s.allocation := rfl


theorem lpReplicaOrbitFourColorSlotRecolor_involutive
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (X Y : Finset (LPReplicaOrbitCommonSlot G sites q)) :
    Function.Involutive
      (lpReplicaOrbitFourColorSlotRecolor G sites q X Y) := by
  intro s
  apply LPReplicaOrbitFourColorSlotState.ext
  · rfl
  · exact balancedSwap_involutive Finset.univ X Y s.color


theorem lpReplicaOrbitFourColorSlotReflect_involutive
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (LPReplicaOrbitCommonSlot G sites q)) :
    Function.Involutive (lpReplicaOrbitFourColorSlotReflect G sites q P) := by
  intro s
  apply LPReplicaOrbitFourColorSlotState.ext
  · funext e
    simp [lpReplicaOrbitFourColorSlotReflect]
  · rfl


theorem lpReplicaOrbitFourColorSlotCrossRecolor_involutive
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P X Y : Finset (LPReplicaOrbitCommonSlot G sites q)) :
    Function.Involutive
      (lpReplicaOrbitFourColorSlotCrossRecolor G sites q P X Y) := by
  intro s
  apply LPReplicaOrbitFourColorSlotState.ext
  · funext e
    simp [lpReplicaOrbitFourColorSlotCrossRecolor,
      lpReplicaOrbitFourColorSlotRecolor,
      lpReplicaOrbitFourColorSlotReflect]
  · exact balancedSwap_involutive Finset.univ X Y s.color


theorem lpReplicaOrbitFourColorSlotCrossToggle_involutive
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (LPReplicaOrbitCommonSlot G sites q)) :
    Function.Involutive
      (lpReplicaOrbitFourColorSlotCrossToggle G sites q P) := by
  intro s
  apply LPReplicaOrbitFourColorSlotState.ext
  · change (lpReplicaOrbitFourColorSlotReflect G sites q P
        (lpReplicaOrbitFourColorSlotReflect G sites q P s)).allocation =
      s.allocation
    exact congrArg (fun z => z.allocation)
      (lpReplicaOrbitFourColorSlotReflect_involutive G sites q P s)
  · change (lpReplicaOrbitFourColorSlotRowToggle G sites q P
        (lpReplicaOrbitFourColorSlotRowToggle G sites q P s)).color =
      s.color
    exact congrArg (fun z => z.color)
      (lpReplicaOrbitFourColorSlotRowToggle_involutive G sites q P s)


theorem lpReplicaOrbitFourColorSlotCrossToggle_comp
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P Q : Finset (LPReplicaOrbitCommonSlot G sites q))
    (s : LPReplicaOrbitFourColorSlotState G sites q) :
    lpReplicaOrbitFourColorSlotCrossToggle G sites q P
        (lpReplicaOrbitFourColorSlotCrossToggle G sites q Q s) =
      lpReplicaOrbitFourColorSlotCrossToggle G sites q (P ∆ Q) s := by
  classical
  apply LPReplicaOrbitFourColorSlotState.ext
  · funext e
    ext k
    have hpq :
        ((Sum.inr ⟨e, k⟩ : LPReplicaOrbitCommonSlot G sites q) ∈ P ∆ Q) ↔
          (((Sum.inr ⟨e, k⟩ : LPReplicaOrbitCommonSlot G sites q) ∈ P ∧
              (Sum.inr ⟨e, k⟩ : LPReplicaOrbitCommonSlot G sites q) ∉ Q) ∨
            ((Sum.inr ⟨e, k⟩ : LPReplicaOrbitCommonSlot G sites q) ∈ Q ∧
              (Sum.inr ⟨e, k⟩ : LPReplicaOrbitCommonSlot G sites q) ∉ P)) :=
      Finset.mem_symmDiff
    simp only [lpReplicaOrbitFourColorSlotCrossToggle,
      lpReplicaOrbitFourColorSlotRowToggle,
      lpReplicaOrbitFourColorSlotReflect,
      lpReplicaOrbitFourColorSelectedStrictSlots,
      Finset.mem_symmDiff, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases ha : k ∈ s.allocation e <;>
      by_cases hp : (Sum.inr ⟨e, k⟩ :
        LPReplicaOrbitCommonSlot G sites q) ∈ P <;>
      by_cases hq : (Sum.inr ⟨e, k⟩ :
        LPReplicaOrbitCommonSlot G sites q) ∈ Q
    all_goals simp [ha, hp, hq]
    all_goals tauto
  · funext x
    change (if x.1 ∈ P then lpReplicaRowToggleFin4
          (if x.1 ∈ Q then lpReplicaRowToggleFin4 (s.color x)
            else s.color x)
        else if x.1 ∈ Q then lpReplicaRowToggleFin4 (s.color x)
          else s.color x) =
      if x.1 ∈ P ∆ Q then lpReplicaRowToggleFin4 (s.color x)
        else s.color x
    by_cases hp : x.1 ∈ P <;> by_cases hq : x.1 ∈ Q
    · have hpq : x.1 ∉ P ∆ Q := by
        rw [Finset.mem_symmDiff]
        simp [hp, hq]
      simp only [hp, if_pos, hq, hpq]
      exact lpReplicaRowToggleFin4_involutive (s.color x)
    · have hpq : x.1 ∈ P ∆ Q := (Finset.mem_symmDiff.mpr
        (Or.inl ⟨hp, hq⟩))
      simp only [hp, if_pos, hq, hpq]
      simp
    · have hpq : x.1 ∈ P ∆ Q := (Finset.mem_symmDiff.mpr
        (Or.inr ⟨hq, hp⟩))
      simp only [hp, hq, if_pos, hpq]
      simp
    · have hpq : x.1 ∉ P ∆ Q := by
        rw [Finset.mem_symmDiff]
        simp [hp, hq]
      simp only [hp, hq, hpq]
      simp


end
end StatMech.Ising
