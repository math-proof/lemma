/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointRace.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLocalBallot.Part5
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFourthMoment
import Def.StatisticalMechanics.Code.Universality.IsingFermionicEndpointRace.Part2


namespace StatMech.Universality

open Finset

noncomputable section

theorem endpointFirstBoundaryExtend_injective (m K : Nat) :
    Function.Injective (endpointFirstBoundaryExtend m K) := by
  rintro ⟨aj, ap, atail⟩ ⟨bj, bp, btail⟩ hab
  have hfull : ap.1 ++ atail.1 = bp.1 ++ btail.1 :=
    congrArg Subtype.val hab
  have hj : (aj : Nat) = bj := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hbavoid := bp.2.2.2 (aj : Nat) hlt
      apply hbavoid
      have ht := congrArg (fun z : List Bool => z.take (aj : Nat)) hfull
      change (ap.1 ++ atail.1).take (aj : Nat) =
        (bp.1 ++ btail.1).take (aj : Nat) at ht
      have haTake : (ap.1 ++ atail.1).take (aj : Nat) = ap.1 := by
        simpa [ap.2.1] using
          (List.take_left (l₁ := ap.1) (l₂ := atail.1))
      have hbTake : (bp.1 ++ btail.1).take (aj : Nat) =
          bp.1.take (aj : Nat) := by
        apply List.take_append_of_le_length
        rw [bp.2.1]
        omega
      rw [haTake, hbTake] at ht
      rw [← ht]
      exact ap.2.2.1
    · have haavoid := ap.2.2.2 (bj : Nat) hgt
      apply haavoid
      have ht := congrArg (fun z : List Bool => z.take (bj : Nat)) hfull
      change (ap.1 ++ atail.1).take (bj : Nat) =
        (bp.1 ++ btail.1).take (bj : Nat) at ht
      have haTake : (ap.1 ++ atail.1).take (bj : Nat) =
          ap.1.take (bj : Nat) := by
        apply List.take_append_of_le_length
        rw [ap.2.1]
        omega
      have hbTake : (bp.1 ++ btail.1).take (bj : Nat) = bp.1 := by
        simpa [bp.2.1] using
          (List.take_left (l₁ := bp.1) (l₂ := btail.1))
      rw [haTake, hbTake] at ht
      rw [ht]
      exact bp.2.2.1
  have hjSubtype : aj = bj := Fin.ext hj
  subst bj
  have hpref : ap.1 = bp.1 := by
    have ht := congrArg (fun z : List Bool => z.take (aj : Nat)) hfull
    simpa [ap.2.1, bp.2.1] using ht
  have htail : atail.1 = btail.1 := by
    have hd := congrArg (fun z : List Bool => z.drop (aj : Nat)) hfull
    simpa [ap.2.1, bp.2.1] using hd
  have hap : ap = bp := Subtype.ext hpref
  have hat : atail = btail := Subtype.ext htail
  subst bp
  subst btail
  rfl

end
end StatMech.Universality
