/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBallot.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKernelCoupling.Part10
import Def.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part7


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem horizontalFirstHitBelowReflect_injective
    (t : Nat) (start level : Int) :
    Function.Injective (horizontalFirstHitBelowReflect t start level) := by
  intro a b h
  apply Subtype.ext
  have hsplit := congrArg
    (fun z : HorizontalFirstHitBelow t (2 * level - start) level => z.1) h
  cases a with
  | mk a ha =>
      cases b with
      | mk b hb =>
          cases a with
          | mk ab aa ahit =>
              cases b with
              | mk bb ba bhit =>
                  simp only [horizontalFirstHitBelowReflect, reflectPrefix] at hsplit
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
                        (reflectedEndpoint level (start, 0)) level => w.before) hsplit
                    exact (Function.Injective.list_map hreflect) hmap
                  have hafter : aa = ba := congrArg
                    (fun w : IsingDiagonalWalkHitSplit
                      (reflectedEndpoint level (start, 0)) level => w.after) hsplit
                  subst bb
                  subst ba
                  rfl

end
end StatMech.Universality
