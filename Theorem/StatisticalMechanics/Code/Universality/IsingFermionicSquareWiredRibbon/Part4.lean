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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredRibbon.Part4
open Equiv SimpleGraph


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

set_option maxHeartbeats 1000000 in
theorem fkIsingSquareWiredCompletedLoopGraph_adj_iff
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (x y : FKIsingSquareWiredCarrier n) :
    (fkIsingSquareWiredCompletedLoopGraph n hn omega).Adj x y ↔
      y = fkIsingSquareWiredTransitionEquiv n hn omega x ∨
      y = fkIsingSquareWiredCompletedIncidenceEquiv n x := by
  cases x <;> cases y <;>
    simp [fkIsingSquareWiredCompletedLoopGraph,
      fkIsingSquareWiredLoopGraph, fkIsingSquareWiredTransitionEquiv,
      fkIsingSquareWiredCompletedIncidenceEquiv, SimpleGraph.edge_adj,
      fkIsingSquareWiredTransitionMate, fkIsingSquareWiredIncidenceMate,
      or_comm]

theorem fkIsingSquareWiredCompletedLoopGraph_adj_color_ne
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {x y : FKIsingSquareWiredCarrier n}
    (hxy : (fkIsingSquareWiredCompletedLoopGraph n hn omega).Adj x y) :
    fkIsingSquareWiredCarrierColor n x ≠
      fkIsingSquareWiredCarrierColor n y := by
  rw [fkIsingSquareWiredCompletedLoopGraph_adj_iff] at hxy
  rcases hxy with rfl | rfl
  · exact (fkIsingSquareWiredCarrierColor_transition_ne n hn omega x).symm
  · exact (fkIsingSquareWiredCarrierColor_completedIncidence_ne n x).symm

theorem fkIsingSquareWiredBoundaryStep_reachable
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (x : FKIsingSquareWiredCarrier n) :
    (fkIsingSquareWiredCompletedLoopGraph n hn omega).Reachable x
      (fkIsingSquareWiredBoundaryStep n hn omega x) := by
  let T := fkIsingSquareWiredTransitionEquiv n hn omega
  let I := fkIsingSquareWiredCompletedIncidenceEquiv n
  have hT : (fkIsingSquareWiredCompletedLoopGraph n hn omega).Adj x (T x) := by
    rw [fkIsingSquareWiredCompletedLoopGraph_adj_iff]
    exact Or.inl rfl
  have hI : (fkIsingSquareWiredCompletedLoopGraph n hn omega).Adj
      (T x) (I (T x)) := by
    rw [fkIsingSquareWiredCompletedLoopGraph_adj_iff]
    exact Or.inr rfl
  exact hT.reachable.trans (by
    simpa only [T, I, fkIsingSquareWiredBoundaryStep, Equiv.trans_apply] using
      hI.reachable)

theorem fkIsingSquareWired_reachable_of_blackBoundary_sameCycle
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (x y : FKIsingSquareWiredBlackCarrier n)
    (hxy : (fkIsingSquareWiredBlackBoundaryPerm n hn omega).SameCycle x y) :
    (fkIsingSquareWiredCompletedLoopGraph n hn omega).Reachable x.1 y.1 := by
  obtain ⟨k, hk⟩ := hxy.exists_nat_pow_eq
  have hpow : ∀ k : Nat,
      (fkIsingSquareWiredCompletedLoopGraph n hn omega).Reachable x.1
        (((fkIsingSquareWiredBlackBoundaryPerm n hn omega) ^ k) x).1 := by
    intro k
    induction k with
    | zero => exact Reachable.refl _
    | succ k ih =>
        rw [pow_succ']
        change (fkIsingSquareWiredCompletedLoopGraph n hn omega).Reachable x.1
          (fkIsingSquareWiredBlackBoundaryPerm n hn omega
            (((fkIsingSquareWiredBlackBoundaryPerm n hn omega) ^ k) x)).1
        exact ih.trans (fkIsingSquareWiredBoundaryStep_reachable n hn omega _)
  simpa only [hk] using hpow k

set_option maxHeartbeats 800000 in
theorem fkIsingSquareWired_blackBoundary_sameCycle_of_walk
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {x y : FKIsingSquareWiredCarrier n}
    (p : (fkIsingSquareWiredCompletedLoopGraph n hn omega).Walk x y)
    (hx : fkIsingSquareWiredCarrierColor n x = false)
    (hy : fkIsingSquareWiredCarrierColor n y = false) :
    (fkIsingSquareWiredBlackBoundaryPerm n hn omega).SameCycle
      ⟨x, hx⟩ ⟨y, hy⟩ := by
  let T := fkIsingSquareWiredTransitionEquiv n hn omega
  let I := fkIsingSquareWiredCompletedIncidenceEquiv n
  induction m : p.length using Nat.strong_induction_on generalizing x y with
  | _ m ih =>
      subst m
      cases p with
      | nil => exact ⟨0, rfl⟩
      | @cons _ v _ hxv p' =>
        cases p' with
        | nil =>
            exact False.elim
              ((fkIsingSquareWiredCompletedLoopGraph_adj_color_ne
                n hn omega hxv) (hx.trans hy.symm))
        | @cons _ w _ hvw rest =>
            have hcv := fkIsingSquareWiredCompletedLoopGraph_adj_color_ne
              n hn omega hxv
            have hvw' := fkIsingSquareWiredCompletedLoopGraph_adj_color_ne
              n hn omega hvw
            have hw : fkIsingSquareWiredCarrierColor n w = false := by
              generalize hcV : fkIsingSquareWiredCarrierColor n v = cv at hcv hvw'
              generalize hcW : fkIsingSquareWiredCarrierColor n w = cw at hvw' ⊢
              cases cv <;> cases cw <;> simp_all
            have htail :
                (fkIsingSquareWiredBlackBoundaryPerm n hn omega).SameCycle
                  ⟨w, hw⟩ ⟨y, hy⟩ :=
              ih rest.length (by simp only [Walk.length_cons]; omega)
                rest hw hy rfl
            have htwo :
                (fkIsingSquareWiredBlackBoundaryPerm n hn omega).SameCycle
                  ⟨x, hx⟩ ⟨w, hw⟩ := by
              rw [fkIsingSquareWiredCompletedLoopGraph_adj_iff] at hxv hvw
              rcases hxv with hxv | hxv <;> rcases hvw with hvw | hvw
              · have hxw : x = w := by
                  rw [hvw, hxv]
                  exact (T.symm_apply_apply x).symm
                exact (Subtype.ext hxw).sameCycle _
              · have hstep :
                    (fkIsingSquareWiredBlackBoundaryPerm n hn omega
                      ⟨x, hx⟩).1 = w := by
                  simp only [fkIsingSquareWiredBlackBoundaryPerm,
                    fkIsingSquareWiredBoundaryStep, Equiv.Perm.subtypePerm_apply,
                    Equiv.trans_apply]
                  rw [hvw, hxv]
                refine ⟨1, ?_⟩
                apply Subtype.ext
                simpa only [zpow_one] using hstep
              · have hstep :
                    (fkIsingSquareWiredBlackBoundaryPerm n hn omega
                      ⟨w, hw⟩).1 = x := by
                  simp only [fkIsingSquareWiredBlackBoundaryPerm,
                    fkIsingSquareWiredBoundaryStep, Equiv.Perm.subtypePerm_apply,
                    Equiv.trans_apply]
                  rw [hvw]
                  have hT : T (T v) = v := T.symm_apply_apply v
                  rw [hT, hxv]
                  exact I.symm_apply_apply x
                apply Equiv.Perm.SameCycle.symm
                refine ⟨1, ?_⟩
                apply Subtype.ext
                simpa only [zpow_one] using hstep
              · have hxw : x = w := by
                  rw [hvw, hxv]
                  exact (I.symm_apply_apply x).symm
                exact (Subtype.ext hxw).sameCycle _
            exact htwo.trans htail

theorem fkIsingSquareWired_blackBoundary_sameCycle_iff_reachable
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (x y : FKIsingSquareWiredBlackCarrier n) :
    (fkIsingSquareWiredBlackBoundaryPerm n hn omega).SameCycle x y ↔
      (fkIsingSquareWiredCompletedLoopGraph n hn omega).Reachable x.1 y.1 := by
  constructor
  · exact fkIsingSquareWired_reachable_of_blackBoundary_sameCycle
      n hn omega x y
  · rintro ⟨p⟩
    exact fkIsingSquareWired_blackBoundary_sameCycle_of_walk
      n hn omega p x.2 y.2

end
end StatMech.Universality
