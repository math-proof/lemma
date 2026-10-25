/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflectionEstimates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLineGambler.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectionEstimates.Part7


namespace StatMech.Universality

namespace IsingDiagonalWalkHitSplit

noncomputable instance survivalExceptionalFirstHitFamilyAll_finite
    (R walkLength : Nat) (start : Int × Int) (level : Int) :
    Finite (SurvivalExceptionalFirstHitFamilyAll R start level
      walkLength) := by
  letI : Fintype
      {bits : List (Bool × Bool) // bits.length = walkLength} :=
    (List.finite_length_eq (Bool × Bool) walkLength).fintype
  exact Finite.of_injective
    (fun w : SurvivalExceptionalFirstHitFamilyAll R start level
      walkLength => firstHitFamilyCode w.2.1.1)
    (by
      intro a b h
      have hsteps := encodePath_injective_of_valid
        a.2.1.1.2.2.1 b.2.1.1.2.2.1 (congrArg Subtype.val h)
      have haSome := firstHitSplit_eq_some a.2.1.1.1 a.2.1.1.2.1
      have hbSome := firstHitSplit_eq_some b.2.1.1.1 b.2.1.1.2.1
      have horiginal : a.2.1.1.1 = b.2.1.1.1 := by
        apply Option.some.inj
        rw [← haSome, ← hbSome, hsteps]
      have htarget : a.1 = b.1 := by
        have haend := a.2.1.1.2.2.2.2
        have hbend := b.2.1.1.2.2.2.2
        rw [← haend, ← hbend, horiginal]
      cases a with
      | mk atarget aw =>
        cases b with
        | mk btarget bw =>
          dsimp at htarget horiginal
          subst btarget
          apply Sigma.ext
          · rfl
          · apply heq_of_eq
            apply Subtype.ext
            apply Subtype.ext
            apply Subtype.ext
            exact horiginal)

end IsingDiagonalWalkHitSplit
end StatMech.Universality
