/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredRibbon.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredCompletion.Part19
import Theorem.StatisticalMechanics.Code.FrontierA.PermCycleQuotientCount.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.FKTutte
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredRibbon.Part7
open Equiv SimpleGraph


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareWiredBlackLocalSwap_isSwap
    (n : Nat) (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    (fkIsingSquareWiredBlackLocalSwap n e).IsSwap := by
  exact ⟨_, _, fkIsingSquareWiredBlackWest_ne_east n e, rfl⟩

theorem fkIsingSquareWiredBlackLocalSwap_apply_of_edge_ne
    (n : Nat) {e f : FKIsingMedialVertex (fkSquareBoxPlanar n)}
    (hef : e ≠ f) (x : FKIsingSquareWiredBlackCarrier n)
    (hx : x.1 = .dart (f, .west) ∨ x.1 = .dart (f, .east)) :
    fkIsingSquareWiredBlackLocalSwap n e x = x := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro h
    have hval := congrArg Subtype.val h
    rcases hx with hx | hx <;> simp [fkIsingSquareWiredBlackWest, hx] at hval
    all_goals exact hef hval.symm
  · intro h
    have hval := congrArg Subtype.val h
    rcases hx with hx | hx <;> simp [fkIsingSquareWiredBlackEast, hx] at hval
    all_goals exact hef hval.symm

theorem fkIsingSquareWiredBlackLocalSwap_commute
    (n : Nat) {e f : FKIsingMedialVertex (fkSquareBoxPlanar n)}
    (hef : e ≠ f) :
    Commute (fkIsingSquareWiredBlackLocalSwap n e)
      (fkIsingSquareWiredBlackLocalSwap n f) := by
  have hww : fkIsingSquareWiredBlackWest n e ≠
      fkIsingSquareWiredBlackWest n f := by
    intro h
    apply hef
    simpa [fkIsingSquareWiredBlackWest] using congrArg Subtype.val h
  have hwe : fkIsingSquareWiredBlackWest n e ≠
      fkIsingSquareWiredBlackEast n f := by
    intro h
    simpa [fkIsingSquareWiredBlackWest,
      fkIsingSquareWiredBlackEast] using congrArg Subtype.val h
  have hew : fkIsingSquareWiredBlackEast n e ≠
      fkIsingSquareWiredBlackWest n f := by
    intro h
    simpa [fkIsingSquareWiredBlackWest,
      fkIsingSquareWiredBlackEast] using congrArg Subtype.val h
  have hee : fkIsingSquareWiredBlackEast n e ≠
      fkIsingSquareWiredBlackEast n f := by
    intro h
    apply hef
    simpa [fkIsingSquareWiredBlackEast] using congrArg Subtype.val h
  have hnodup : [fkIsingSquareWiredBlackWest n e,
      fkIsingSquareWiredBlackEast n e,
      fkIsingSquareWiredBlackWest n f,
      fkIsingSquareWiredBlackEast n f].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false, not_or]
    exact ⟨⟨fkIsingSquareWiredBlackWest_ne_east n e,
      hww, hwe⟩, ⟨⟨hew, hee⟩,
        fkIsingSquareWiredBlackWest_ne_east n f,
        by simp, List.nodup_nil⟩⟩
  exact (Equiv.Perm.disjoint_swap_swap hnodup).commute

theorem fkIsingSquareWiredTransitionMate_setOpen_black
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (x : FKIsingSquareWiredBlackCarrier n) :
    fkIsingSquareWiredTransitionMate n hn (setOpen e.1 omega) x.1 =
      fkIsingSquareWiredTransitionMate n hn (setClosed e.1 omega)
        (fkIsingSquareWiredBlackLocalSwap n e x).1 := by
  rcases x with ⟨x, hx⟩
  cases x with
  | source =>
      have hswap : fkIsingSquareWiredBlackLocalSwap n e
          ⟨.source, hx⟩ = ⟨.source, hx⟩ := by
        apply Equiv.swap_apply_of_ne_of_ne
        · intro h
          simpa [fkIsingSquareWiredBlackWest] using congrArg Subtype.val h
        · intro h
          simpa [fkIsingSquareWiredBlackEast] using congrArg Subtype.val h
      rw [hswap]
      simp [fkIsingSquareWiredTransitionMate]
  | terminal =>
      have hswap : fkIsingSquareWiredBlackLocalSwap n e
          ⟨.terminal, hx⟩ = ⟨.terminal, hx⟩ := by
        apply Equiv.swap_apply_of_ne_of_ne
        · intro h
          simpa [fkIsingSquareWiredBlackWest] using congrArg Subtype.val h
        · intro h
          simpa [fkIsingSquareWiredBlackEast] using congrArg Subtype.val h
      rw [hswap]
      simp [fkIsingSquareWiredTransitionMate]
  | bond d =>
      have hswap : fkIsingSquareWiredBlackLocalSwap n e
          ⟨.bond d, hx⟩ = ⟨.bond d, hx⟩ := by
        apply Equiv.swap_apply_of_ne_of_ne
        · intro h
          simpa [fkIsingSquareWiredBlackWest] using congrArg Subtype.val h
        · intro h
          simpa [fkIsingSquareWiredBlackEast] using congrArg Subtype.val h
      rw [hswap]
      simp [fkIsingSquareWiredTransitionMate]
  | dart d =>
      rcases d with ⟨f, side⟩
      have hside : side = .west ∨ side = .east := by
        cases side <;> simp_all [fkIsingSquareWiredCarrierColor,
          fkIsingSquareWiredDartSideColor]
      rcases hside with rfl | rfl <;> by_cases hfe : f = e
      · subst f
        simp [fkIsingSquareWiredBlackLocalSwap,
          fkIsingSquareWiredBlackWest, fkIsingSquareWiredBlackEast,
          fkIsingSquareWiredTransitionMate, FKIsingMedialDart.localMate]
      · have hswap := fkIsingSquareWiredBlackLocalSwap_apply_of_edge_ne
          n (Ne.symm hfe) ⟨.dart (f, .west), hx⟩ (Or.inl rfl)
        rw [hswap]
        have hne : f.1 ≠ e.1 := fun h => hfe (Subtype.ext h)
        simp [fkIsingSquareWiredTransitionMate, FKIsingMedialDart.localMate,
          setOpen, setClosed, hne]
      · subst f
        simp [fkIsingSquareWiredBlackLocalSwap,
          fkIsingSquareWiredBlackWest, fkIsingSquareWiredBlackEast,
          fkIsingSquareWiredTransitionMate, FKIsingMedialDart.localMate]
      · have hswap := fkIsingSquareWiredBlackLocalSwap_apply_of_edge_ne
          n (Ne.symm hfe) ⟨.dart (f, .east), hx⟩ (Or.inr rfl)
        rw [hswap]
        have hne : f.1 ≠ e.1 := fun h => hfe (Subtype.ext h)
        simp [fkIsingSquareWiredTransitionMate, FKIsingMedialDart.localMate,
          setOpen, setClosed, hne]

set_option maxHeartbeats 1000000 in
theorem fkIsingSquareWiredBlackBoundaryPerm_setOpen
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    fkIsingSquareWiredBlackBoundaryPerm n hn (setOpen e.1 omega) =
      fkIsingSquareWiredBlackBoundaryPerm n hn (setClosed e.1 omega) *
        fkIsingSquareWiredBlackLocalSwap n e := by
  apply Equiv.ext
  intro x
  apply Subtype.ext
  simp only [fkIsingSquareWiredBlackBoundaryPerm,
    Equiv.Perm.subtypePerm_apply, Equiv.Perm.mul_apply,
    fkIsingSquareWiredBoundaryStep, Equiv.trans_apply]
  exact congrArg (fkIsingSquareWiredCompletedIncidenceEquiv n)
    (fkIsingSquareWiredTransitionMate_setOpen_black n hn omega e x)


end
end StatMech.Universality
