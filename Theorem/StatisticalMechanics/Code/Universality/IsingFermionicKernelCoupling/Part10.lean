/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKernelCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectionEstimates.Part13
import Def.StatisticalMechanics.Code.Universality.IsingFermionicKernelCoupling.Part14


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem killedChoiceNoHitAllProjection_injective
    (R t : Nat) (p : IsingLeapfrogBox R) (level : Int) :
    Function.Injective (killedChoiceNoHitAllProjection R t p level) := by
  intro a b h
  have hx : a.1.1.map Prod.fst = b.1.1.map Prod.fst :=
    congrArg (fun z => z.1.1) h
  have hy : a.1.1.map Prod.snd = b.1.1.map Prod.snd :=
    congrArg (fun z => z.2.1) h
  apply Subtype.ext
  apply Subtype.ext
  exact prodBits_injective hx hy

theorem natCard_killedChoiceNoHitAll_le_horizontal_mul_pow
    (R t : Nat) (p : IsingLeapfrogBox R) (level : Int) :
    Nat.card (IsingLeapfrogKilledChoiceNoHitAll R t p level) ≤
      Nat.card (IsingHorizontalNoHitFamily t (isingLeapfrogBoxInt p).1 level) *
        2 ^ t := by
  calc
    _ ≤ Nat.card (IsingHorizontalNoHitFamily t
          (isingLeapfrogBoxInt p).1 level ×
        {ys : List Bool // ys.length = t}) :=
      Nat.card_le_card_of_injective
        (killedChoiceNoHitAllProjection R t p level)
        (killedChoiceNoHitAllProjection_injective R t p level)
    _ = _ := by
      rw [Nat.card_prod]
      congr 1
      change Nat.card (List.Vector Bool t) = 2 ^ t
      rw [Nat.card_congr (Equiv.vectorEquivFin Bool t),
        Nat.card_eq_fintype_card, Fintype.card_fun]
      simp

end
end StatMech.Universality
