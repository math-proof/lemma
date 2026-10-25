/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKernelCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectionEstimates.Part13
import Def.StatisticalMechanics.Code.Universality.IsingFermionicKernelCoupling.Part7


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

noncomputable instance isingLeapfrogKilledChoiceFirstHitFamily_finite
    (R t : Nat) (p q : IsingLeapfrogBox R) (level : Int) :
    Finite (IsingLeapfrogKilledChoiceFirstHitFamily R t p q level) := by
  letI : Fintype {bs : List (Bool × Bool) // bs.length = t} :=
    (List.finite_length_eq (Bool × Bool) t).fintype
  exact Finite.of_injective
    (fun z : IsingLeapfrogKilledChoiceFirstHitFamily R t p q level =>
      (⟨z.1.1.1, z.1.1.2.1⟩ : {bs : List (Bool × Bool) //
        bs.length = t}))
    (by
      intro a b h
      have hbits : a.1.1.1 = b.1.1.1 := congrArg
        (fun z : {bs : List (Bool × Bool) // bs.length = t} => z.1) h
      have ha := a.2
      have hb := b.2
      have hsplits : a.1.2 = b.1.2 := by
        apply Option.some.inj
        rw [← ha, ← hb, hbits]
      apply Subtype.ext
      apply Prod.ext
      · exact Subtype.ext hbits
      · exact hsplits)


end
end StatMech.Universality
