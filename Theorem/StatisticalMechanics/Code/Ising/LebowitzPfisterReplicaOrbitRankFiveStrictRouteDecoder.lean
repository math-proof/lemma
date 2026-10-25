/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteDecoder.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateStrictRoute.Part2
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPairedCutInjection.Part12
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictRouteDecoder


namespace StatMech.Ising

noncomputable section

open scoped symmDiff

open StatMech.Sharpness.FluxEdgeCopy

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

@[simp] theorem lpReplicaOrbitFourColorSlotReflectRowToggle_allocation
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (spatial row : Finset (LPReplicaOrbitCommonSlot G sites q))
    (s : LPReplicaOrbitFourColorSlotState G sites q) :
    (lpReplicaOrbitFourColorSlotReflectRowToggle
      G sites q spatial row s).allocation =
      (lpReplicaOrbitFourColorSlotReflect
        G sites q spatial s).allocation := rfl

@[simp] theorem lpReplicaOrbitFourColorSlotReflectRowToggle_color
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (spatial row : Finset (LPReplicaOrbitCommonSlot G sites q))
    (s : LPReplicaOrbitFourColorSlotState G sites q)
    (x : ↑(Finset.univ : Finset
      (LPReplicaOrbitCommonSlot G sites q))) :
    (lpReplicaOrbitFourColorSlotReflectRowToggle
      G sites q spatial row s).color x =
      if x.1 ∈ row then lpReplicaRowToggleFin4 (s.color x)
      else s.color x := rfl


theorem lpReplicaOrbitFourColorSlotRowMask_reflectRowToggle
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (spatial row : Finset (LPReplicaOrbitCommonSlot G sites q))
    (s : LPReplicaOrbitFourColorSlotState G sites q) :
    lpReplicaOrbitFourColorSlotRowMask G sites q
        (lpReplicaOrbitFourColorSlotReflectRowToggle
          G sites q spatial row s) =
      lpReplicaOrbitFourColorSlotRowMask G sites q s ∆ row := by
  have h := lpReplicaOrbitFourColorSlotRowMask_crossToggle
    G sites q row s
  change lpReplicaOrbitFourColorSlotRowMask G sites q
      (lpReplicaOrbitFourColorSlotReflectRowToggle
        G sites q spatial row s) = _
  exact h

@[simp] theorem lpReplicaOrbitFourColorSlotStateOfTag_color
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (x : ↑(Finset.univ : Finset
      (LPReplicaOrbitCommonSlot G sites q))) :
    (lpReplicaOrbitFourColorSlotStateOfTag
      G sites q m hm L tag).color x =
      lpReplicaRowTagEquivFin4
        (tag ((lpReplicaProfileCopyEquivCommonSlot
          G sites q m hm L).symm x.1)) := rfl


theorem lpReplicaSingletonFalseRowTag_equivFin4
    {C : Type*} [DecidableEq C] (c a : C) :
    lpReplicaRowTagEquivFin4 (lpReplicaSingletonFalseRowTag c a) =
      if a = c then
        lpReplicaRowToggleFin4 (lpReplicaRowTagEquivFin4 (true, false))
      else lpReplicaRowTagEquivFin4 (true, false) := by
  by_cases h : a = c
  · subst a
    simp [lpReplicaSingletonFalseRowTag, lpReplicaRowToggleFin4,
      lpReplicaRowTagEquivFin4]
  · simp [lpReplicaSingletonFalseRowTag, lpReplicaRowTagEquivFin4, h]


theorem lpReplicaOrbitFourColorSlotReflectRowToggle_involutive
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (spatial row : Finset (LPReplicaOrbitCommonSlot G sites q)) :
    Function.Involutive
      (lpReplicaOrbitFourColorSlotReflectRowToggle
        G sites q spatial row) := by
  intro s
  apply LPReplicaOrbitFourColorSlotState.ext
  · exact congrArg (fun z => z.allocation)
      (lpReplicaOrbitFourColorSlotReflect_involutive
        G sites q spatial s)
  · exact congrArg (fun z => z.color)
      (lpReplicaOrbitFourColorSlotRowToggle_involutive
        G sites q row s)


theorem lpReplicaOrbitFourColorSlotReflectRowToggle_comm
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (spatial₀ spatial₁ row :
      Finset (LPReplicaOrbitCommonSlot G sites q))
    (s : LPReplicaOrbitFourColorSlotState G sites q) :
    lpReplicaOrbitFourColorSlotReflectRowToggle G sites q spatial₀ row
        (lpReplicaOrbitFourColorSlotReflectRowToggle
          G sites q spatial₁ row s) =
      lpReplicaOrbitFourColorSlotReflectRowToggle G sites q spatial₁ row
        (lpReplicaOrbitFourColorSlotReflectRowToggle
          G sites q spatial₀ row s) := by
  apply LPReplicaOrbitFourColorSlotState.ext
  · funext e
    change (s.allocation e ∆
        lpReplicaOrbitFourColorSelectedStrictSlots G sites q spatial₁ e) ∆
          lpReplicaOrbitFourColorSelectedStrictSlots G sites q spatial₀ e =
      (s.allocation e ∆
        lpReplicaOrbitFourColorSelectedStrictSlots G sites q spatial₀ e) ∆
          lpReplicaOrbitFourColorSelectedStrictSlots G sites q spatial₁ e
    rw [symmDiff_assoc, symmDiff_assoc]
    congr 1
    exact symmDiff_comm _ _
  · funext x
    simp only [lpReplicaOrbitFourColorSlotReflectRowToggle_color]


theorem lpReplicaOrbitFourColorSlotReflectRowToggle_crossed
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (spatial₀ spatial₁ row :
      Finset (LPReplicaOrbitCommonSlot G sites q))
    (s t : LPReplicaOrbitFourColorSlotState G sites q)
    (hcross :
      lpReplicaOrbitFourColorSlotReflectRowToggle G sites q spatial₀ row s =
        lpReplicaOrbitFourColorSlotReflectRowToggle
          G sites q spatial₁ row t) :
    lpReplicaOrbitFourColorSlotReflectRowToggle G sites q spatial₁ row s =
      lpReplicaOrbitFourColorSlotReflectRowToggle
        G sites q spatial₀ row t := by
  let F₀ := lpReplicaOrbitFourColorSlotReflectRowToggle
    G sites q spatial₀ row
  let F₁ := lpReplicaOrbitFourColorSlotReflectRowToggle
    G sites q spatial₁ row
  change F₀ s = F₁ t at hcross
  change F₁ s = F₀ t
  calc
    F₁ s = F₁ (F₀ (F₀ s)) := congrArg F₁
      (lpReplicaOrbitFourColorSlotReflectRowToggle_involutive
        G sites q spatial₀ row s).symm
    _ = F₀ (F₁ (F₀ s)) :=
      (lpReplicaOrbitFourColorSlotReflectRowToggle_comm
        G sites q spatial₀ spatial₁ row (F₀ s)).symm
    _ = F₀ (F₁ (F₁ t)) := congrArg (fun u => F₀ (F₁ u)) hcross
    _ = F₀ t := congrArg F₀
      (lpReplicaOrbitFourColorSlotReflectRowToggle_involutive
        G sites q spatial₁ row t)


theorem lpReplicaDecoratedOrbitAtomCanonicalizeRawPartialReflect_slotState
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (rawTag : Copy (lpReplicaCurrentGraph G sites)
      (lpReplicaCollisionProfile G sites
        (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
        (profileFlux (lpReplicaCurrentGraph G sites) m P)) ->
      LPReplicaRowTag)
    (A B : Finset (LPReplicaCurrentVertex V))
    (hraw : LPReplicaRowGate G sites
      (lpReplicaCollisionProfile G sites
        (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
        (profileFlux (lpReplicaCurrentGraph G sites) m P))
      A B rawTag) :
    let target := lpReplicaPartialReflectProfile G sites m
      (profileFlux (lpReplicaCurrentGraph G sites) m P)
    let relabel := lpReplicaPartialReflectCanonicalRelabelEquiv
      G sites q m hm L P
    let tag := lpReplicaTransportTag G sites relabel rawTag
    let atom := lpReplicaDecoratedOrbitAtomCanonicalizeRawPartialReflect
      G sites q m hm L P rawTag A B hraw
    lpReplicaOrientedFourColorSlotState G sites A
        (B.map lpReplicaCurrentReflect.toEmbedding) q
        (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites A
          (B.map lpReplicaCurrentReflect.toEmbedding) q atom) =
      lpReplicaOrbitFourColorSlotStateOfTag G sites q target
        ((lpReplicaSymmetrizedProfile_partialReflectCopies
          G sites m P).trans hm)
        (lpReplicaProfileOrbitLabelPartialReflectCopies
          G sites q m hm P L) tag := by
  dsimp only
  unfold lpReplicaDecoratedOrbitAtomCanonicalizeRawPartialReflect
  apply lpReplicaOrientedFourColorSlotState_ofRowGate

set_option maxHeartbeats 800000 in


theorem lpReplicaOffdiagDecoratedSourceSlotState_eq_rowGateData
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z =
      lpReplicaOrbitFourColorSlotStateOfTag G sites q z.1.1.1
        z.1.1.2 z.2.2
        (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 := by
  change lpReplicaOrbitFourColorSlotStateOfTag G sites q z.1.1.1
      z.1.1.2 z.2.2
      (lpReplicaOrientedFourColorTag G sites ∅
        (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1) q
        (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites ∅
          (lpMatchingSeamSource
              (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
            lpMatchingSeamSource
              (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
            lpMatchingGhostSource
              (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
              lpReplicaCurrentGhost1) q z)) = _
  rw [lpReplicaOffdiagDecoratedSource_orientedTag_eq_rowGateData]


theorem lpReplicaStrictRouteSingletonTag_slotState
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (c d : Copy (lpReplicaCurrentGraph G sites) m)
    (sourceTag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (hsource : ∀ e, sourceTag e = (true, false)) :
    let rawCopy := lpReplicaPartialReflectCopyEquivRaw G sites m {d}
    let rawTag := lpReplicaSingletonFalseRowTag (rawCopy c)
    let target := lpReplicaPartialReflectProfile G sites m
      (profileFlux (lpReplicaCurrentGraph G sites) m {d})
    let relabel := lpReplicaPartialReflectCanonicalRelabelEquiv
      G sites q m hm L {d}
    let targetTag := lpReplicaTransportTag G sites relabel rawTag
    let spatial := lpReplicaOrbitCommonSlotsOfCopies
      G sites q m hm L {d}
    let row := lpReplicaOrbitCommonSlotsOfCopies
      G sites q m hm L {c}
    lpReplicaOrbitFourColorSlotStateOfTag G sites q target
        ((lpReplicaSymmetrizedProfile_partialReflectCopies
          G sites m {d}).trans hm)
        (lpReplicaProfileOrbitLabelPartialReflectCopies
          G sites q m hm {d} L) targetTag =
      lpReplicaOrbitFourColorSlotReflectRowToggle G sites q spatial row
        (lpReplicaOrbitFourColorSlotStateOfTag
          G sites q m hm L sourceTag) := by
  classical
  dsimp only
  apply LPReplicaOrbitFourColorSlotState.ext
  · exact lpReplicaProfileOrbitLabelPartialReflectCopies_allocation_commonSlots
      G sites q m hm L {d} sourceTag
  · funext x
    let Es := lpReplicaProfileCopyEquivCommonSlot G sites q m hm L
    let target := lpReplicaPartialReflectProfile G sites m
      (profileFlux (lpReplicaCurrentGraph G sites) m {d})
    let Lt := lpReplicaProfileOrbitLabelPartialReflectCopies
      G sites q m hm {d} L
    let Et := lpReplicaProfileCopyEquivCommonSlot G sites q target
      ((lpReplicaSymmetrizedProfile_partialReflectCopies
        G sites m {d}).trans hm) Lt
    let Ecanon := lpReplicaPartialReflectCanonicalCopyEquiv
      G sites q m hm L {d}
    let Eraw := lpReplicaPartialReflectCopyEquivRaw G sites m {d}
    have hslot : Ecanon (Es.symm x.1) = Et.symm x.1 := by
      apply Et.injective
      dsimp only [Ecanon, lpReplicaPartialReflectCanonicalCopyEquiv,
        Equiv.trans_apply]
      rw [Es.apply_symm_apply, Et.apply_symm_apply]
    have hpre :
        (lpReplicaPartialReflectCanonicalRelabelEquiv
          G sites q m hm L {d}).symm (Et.symm x.1) =
          Eraw (Es.symm x.1) := by
      unfold lpReplicaPartialReflectCanonicalRelabelEquiv
      change Eraw (Ecanon.symm (Et.symm x.1)) = Eraw (Es.symm x.1)
      rw [← hslot, Ecanon.symm_apply_apply]
    have hrow : x.1 ∈ lpReplicaOrbitCommonSlotsOfCopies
        G sites q m hm L {c} ↔ Es.symm x.1 = c := by
      rw [mem_lpReplicaOrbitCommonSlotsOfCopies_iff]
      change Es.symm x.1 ∈ {c} ↔ Es.symm x.1 = c
      simp only [Finset.mem_singleton]
    rw [lpReplicaOrbitFourColorSlotStateOfTag_color,
      lpReplicaOrbitFourColorSlotReflectRowToggle_color,
      lpReplicaOrbitFourColorSlotStateOfTag_color]
    simp only [lpReplicaTransportTag]
    rw [hpre, hsource,
      lpReplicaSingletonFalseRowTag_equivFin4]
    change (if Eraw (Es.symm x.1) = Eraw c then _ else _) = _
    by_cases hxc : Es.symm x.1 = c
    · rw [if_pos (congrArg Eraw hxc), if_pos (hrow.mpr hxc)]
    · rw [if_neg (fun h => hxc (Eraw.injective h)),
        if_neg (fun hx => hxc (hrow.mp hx))]

set_option maxHeartbeats 800000 in


theorem lpReplicaOffdiagDecoratedSourceCanonicalSingletonStrictRoute_slotState
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (c d : Copy (lpReplicaCurrentGraph G sites) z.1.1.1)
    (A B : Finset (LPReplicaCurrentVertex V))
    (hraw : LPReplicaRowGate G sites
      (lpReplicaCollisionProfile G sites
        (profileFlux (lpReplicaCurrentGraph G sites) z.1.1.1
          (Finset.univ \ {d}))
        (profileFlux (lpReplicaCurrentGraph G sites) z.1.1.1 {d}))
      A B
      (lpReplicaSingletonFalseRowTag
        (lpReplicaPartialReflectCopyEquivRaw
          G sites z.1.1.1 {d} c)))
    (hsource : ∀ e,
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 e =
        (true, false)) :
    let atom := lpReplicaDecoratedOrbitAtomCanonicalizeRawPartialReflect
      G sites q z.1.1.1 z.1.1.2 z.2.2 {d}
      (lpReplicaSingletonFalseRowTag
        (lpReplicaPartialReflectCopyEquivRaw
          G sites z.1.1.1 {d} c)) A B hraw
    lpReplicaOrientedFourColorSlotState G sites A
        (B.map lpReplicaCurrentReflect.toEmbedding) q
        (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites A
          (B.map lpReplicaCurrentReflect.toEmbedding) q atom) =
      lpReplicaOrbitFourColorSlotReflectRowToggle G sites q
        (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
          z.1.1.2 z.2.2 {d})
        (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
          z.1.1.2 z.2.2 {c})
        (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z) := by
  dsimp only
  rw [lpReplicaDecoratedOrbitAtomCanonicalizeRawPartialReflect_slotState]
  rw [lpReplicaStrictRouteSingletonTag_slotState G sites q z.1.1.1
    z.1.1.2 z.2.2 c d
    (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 hsource]
  exact congrArg
    (lpReplicaOrbitFourColorSlotReflectRowToggle G sites q
      (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
        z.1.1.2 z.2.2 {d})
      (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
        z.1.1.2 z.2.2 {c}))
    (lpReplicaOffdiagDecoratedSourceSlotState_eq_rowGateData
      G sites i j q z).symm


theorem lpReplicaOffdiagDecoratedSource_eq_of_strictRouteState_collision
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z w : LPReplicaOffdiagDecoratedSource G sites i j q)
    (spatialZ rowZ spatialW rowW :
      Finset (LPReplicaOrbitCommonSlot G sites q))
    (targetZ targetW : LPReplicaOrbitFourColorSlotState G sites q)
    (hz : targetZ =
      lpReplicaOrbitFourColorSlotReflectRowToggle G sites q spatialZ rowZ
        (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z))
    (hw : targetW =
      lpReplicaOrbitFourColorSlotReflectRowToggle G sites q spatialW rowW
        (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q w))
    (hspatial : spatialZ = spatialW) (hrow : rowZ = rowW)
    (htarget : targetZ = targetW) :
    z = w := by
  subst spatialW
  subst rowW
  apply lpReplicaOffdiagDecoratedSourceSlotState_injective G sites i j q
  apply (lpReplicaOrbitFourColorSlotReflectRowToggle_involutive
    G sites q spatialZ rowZ).injective
  exact hz.symm.trans (htarget.trans hw)


end
end StatMech.Ising
