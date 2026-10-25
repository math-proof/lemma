/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalBallot.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedPointwise.Part3
import Instance.StatisticalMechanics.Code.Universality.IsingFermionicLocalBallot


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem natCard_localHorizontalFree_eq_hit_add_noHit
    (t : Nat) (start level target : Int) :
    Nat.card (LocalHorizontalFreeFiber t start target) =
      Nat.card (LocalHorizontalHitFiber t start level target) +
        Nat.card (LocalHorizontalNoHitFiber t start level target) := by
  rw [← Nat.card_sum]
  exact Nat.card_congr
    (Equiv.sumCompl (fun w : LocalHorizontalFreeFiber t start target =>
      isingDiagonalWalkFirstHitSplit? (start, 0) level
        (localHorizontalSteps w.1) ≠ none)).symm

theorem reflectPrefix_steps_vertical
    {start : Int × Int} {level : Int}
    (split : IsingDiagonalWalkHitSplit start level)
    (hvertical : ∀ d ∈ split.steps, d.2 = 1) :
    ∀ d ∈ split.reflectPrefix.steps, d.2 = 1 := by
  intro d hd
  change d ∈ split.before.map reflectIncrement ++ split.after at hd
  rcases List.mem_append.mp hd with hd | hd
  · rcases List.mem_map.mp hd with ⟨e, he, rfl⟩
    simpa [reflectIncrement] using hvertical e
      (List.mem_append.mpr (Or.inl he))
  · exact hvertical d (List.mem_append.mpr (Or.inr hd))

theorem reflectPrefix_injective
    {start : Int × Int} {level : Int} :
    Function.Injective
      (IsingDiagonalWalkHitSplit.reflectPrefix (start := start) (level := level)) := by
  intro a b h
  cases a with
  | mk ab aa ahit =>
      cases b with
      | mk bb ba bhit =>
          simp only [IsingDiagonalWalkHitSplit.reflectPrefix] at h
          have hbefore : ab = bb := by
            have hreflect : Function.Injective reflectIncrement := by
              intro x y hxy
              apply Prod.ext
              · have hx := congrArg Prod.fst hxy
                simp [reflectIncrement] at hx
                linarith
              · simpa [reflectIncrement] using congrArg Prod.snd hxy
            have hmap := congrArg
              (fun w : IsingDiagonalWalkHitSplit
                (reflectedEndpoint level start) level => w.before) h
            exact (Function.Injective.list_map hreflect) hmap
          have hafter : aa = ba := congrArg
            (fun w : IsingDiagonalWalkHitSplit
              (reflectedEndpoint level start) level => w.after) h
          subst bb
          subst ba
          rfl

end
end StatMech.Universality
