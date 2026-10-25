/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteDecoder.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateStrictRoute.Part2
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPairedCutInjection.Part12
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictRouteDecoder.Part2


namespace StatMech.Ising

noncomputable section

open scoped symmDiff

open StatMech.Sharpness.FluxEdgeCopy

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem LPReplicaStrictRouteStateFamily.target_fiber_card_le_twenty
    {G : SimpleGraph V} {sites : I -> V} {i j : I}
    {q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat}
    {Source Target : Type*} [Fintype Source] [DecidableEq Target]
    (F : LPReplicaStrictRouteStateFamily
      G sites i j q Source Target)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (t : Target) :
    Fintype.card {x : Source // F.target x = t} ≤ 20 := by
  classical
  calc
    Fintype.card {x : Source // F.target x = t} ≤
        Fintype.card (LPReplicaStrictRouteMaskKey G sites q) :=
      Fintype.card_le_of_embedding (F.targetFiberRouteKeyEmbedding t)
    _ = 20 := card_lpReplicaStrictRouteMaskKey_rankFive G sites q hcard


theorem LPReplicaStrictRouteStateFamily.rowSlot_eq_of_target_eq
    {G : SimpleGraph V} {sites : I -> V} {i j : I}
    {q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat}
    {Source Target : Type*}
    (F : LPReplicaStrictRouteStateFamily
      G sites i j q Source Target)
    (hsourceRow : ∀ x,
      lpReplicaOrbitFourColorSlotRowMask G sites q
        (lpReplicaOffdiagDecoratedSourceSlotState
          G sites i j q (F.source x)) = Finset.univ)
    {x y : Source} (htarget : F.target x = F.target y) :
    F.rowSlot x = F.rowSlot y := by
  have hstate := congrArg F.targetState htarget
  rw [F.output_state x, F.output_state y] at hstate
  have hmask := congrArg
    (lpReplicaOrbitFourColorSlotRowMask G sites q) hstate
  rw [lpReplicaOrbitFourColorSlotRowMask_reflectRowToggle,
    lpReplicaOrbitFourColorSlotRowMask_reflectRowToggle,
    hsourceRow x, hsourceRow y] at hmask
  exact Finset.singleton_injective
    (symmDiff_right_injective (Finset.univ : Finset
      (LPReplicaOrbitCommonSlot G sites q)) hmask)


theorem LPReplicaStrictRouteStateFamily.eq_of_spatialSlot_eq_of_target_eq
    {G : SimpleGraph V} {sites : I -> V} {i j : I}
    {q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat}
    {Source Target : Type*}
    (F : LPReplicaStrictRouteStateFamily
      G sites i j q Source Target)
    (hsourceRow : ∀ x,
      lpReplicaOrbitFourColorSlotRowMask G sites q
        (lpReplicaOffdiagDecoratedSourceSlotState
          G sites i j q (F.source x)) = Finset.univ)
    {x y : Source} (hspatial : F.spatialSlot x = F.spatialSlot y)
    (htarget : F.target x = F.target y) : x = y := by
  apply F.source.injective
  apply lpReplicaOffdiagDecoratedSource_eq_of_strictRouteState_collision
    G sites i j q (F.source x) (F.source y)
    {F.spatialSlot x} {F.rowSlot x}
    {F.spatialSlot y} {F.rowSlot y}
    (F.targetState (F.target x)) (F.targetState (F.target y))
    (F.output_state x) (F.output_state y)
  · exact congrArg
      (fun s : LPReplicaOrbitCommonSlot G sites q => ({s} : Finset _))
      hspatial
  · exact congrArg
      (fun s : LPReplicaOrbitCommonSlot G sites q => ({s} : Finset _))
      (F.rowSlot_eq_of_target_eq hsourceRow htarget)
  · exact congrArg F.targetState htarget


theorem LPReplicaStrictRouteStateFamily.saturated_target_fiber_card_le_four
    {G : SimpleGraph V} {sites : I -> V} {i j : I}
    {q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat}
    {Source Target : Type*} [Fintype Source] [DecidableEq Target]
    (F : LPReplicaStrictRouteStateFamily
      G sites i j q Source Target)
    (hsourceRow : ∀ x,
      lpReplicaOrbitFourColorSlotRowMask G sites q
        (lpReplicaOffdiagDecoratedSourceSlotState
          G sites i j q (F.source x)) = Finset.univ)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (t : Target) :
    Fintype.card {x : Source // F.target x = t} ≤ 4 := by
  classical
  let Fiber := {x : Source // F.target x = t}
  by_cases hne : Nonempty Fiber
  · let base : Fiber := Classical.choice hne
    let encode : Fiber ↪
        {d : LPReplicaOrbitCommonSlot G sites q //
          d ≠ F.rowSlot base.1} :=
      {
        toFun := fun x => ⟨F.spatialSlot x.1, by
          intro hspatialRow
          apply F.slots_ne x.1
          exact hspatialRow.trans
            (F.rowSlot_eq_of_target_eq hsourceRow
              (x.2.trans base.2.symm)).symm⟩
        inj' := by
          intro x y h
          apply Subtype.ext
          apply F.eq_of_spatialSlot_eq_of_target_eq hsourceRow
          · exact congrArg Subtype.val h
          · exact x.2.trans y.2.symm
      }
    calc
      Fintype.card Fiber ≤
          Fintype.card {d : LPReplicaOrbitCommonSlot G sites q //
            d ≠ F.rowSlot base.1} :=
        Fintype.card_le_of_embedding encode
      _ = Fintype.card (LPReplicaOrbitCommonSlot G sites q) - 1 :=
        Set.card_ne_eq (F.rowSlot base.1)
      _ = 4 := by omega
  · have hi : IsEmpty Fiber := not_nonempty_iff.mp hne
    rw [(Fintype.card_eq_zero_iff.mpr hi)]
    omega


theorem LPReplicaStrictRouteStateFamily.card_le_twenty_mul_target
    {G : SimpleGraph V} {sites : I -> V} {i j : I}
    {q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat}
    {Source Target : Type*} [Fintype Source] [Fintype Target]
    (F : LPReplicaStrictRouteStateFamily
      G sites i j q Source Target)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
    Fintype.card Source ≤ 20 * Fintype.card Target := by
  let encode : Source ↪
      LPReplicaStrictRouteMaskKey G sites q × Target :=
    {
      toFun := fun x => (F.routeKey x, F.target x)
      inj' := by
        intro x y h
        apply F.source.injective
        have hkey := congrArg Prod.fst h
        have htarget := congrArg Prod.snd h
        have hpair := congrArg Subtype.val hkey
        apply lpReplicaOffdiagDecoratedSource_eq_of_strictRouteState_collision
          G sites i j q (F.source x) (F.source y)
          {F.spatialSlot x} {F.rowSlot x}
          {F.spatialSlot y} {F.rowSlot y}
          (F.targetState (F.target x)) (F.targetState (F.target y))
          (F.output_state x) (F.output_state y)
        · exact congrArg
            (fun s : LPReplicaOrbitCommonSlot G sites q =>
              ({s} : Finset _))
            (congrArg Prod.fst hpair)
        · exact congrArg
            (fun s : LPReplicaOrbitCommonSlot G sites q =>
              ({s} : Finset _))
            (congrArg Prod.snd hpair)
        · exact congrArg F.targetState htarget
    }
  calc
    Fintype.card Source ≤
        Fintype.card (LPReplicaStrictRouteMaskKey G sites q × Target) :=
      Fintype.card_le_of_embedding encode
    _ = Fintype.card (LPReplicaStrictRouteMaskKey G sites q) *
        Fintype.card Target := Fintype.card_prod _ _
    _ = 20 * Fintype.card Target := by
      rw [card_lpReplicaStrictRouteMaskKey_rankFive G sites q hcard]

end
end StatMech.Ising
