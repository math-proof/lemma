/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKernelCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectionEstimates.Part13
import Def.StatisticalMechanics.Code.Universality.IsingFermionicKernelCoupling.Part11


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

noncomputable instance isingLeapfrogKilledChoiceNoHitAll_finite
    (R t : Nat) (p : IsingLeapfrogBox R) (level : Int) :
    Finite (IsingLeapfrogKilledChoiceNoHitAll R t p level) := by
  letI : Fintype {bs : List (Bool × Bool) // bs.length = t} :=
    (List.finite_length_eq (Bool × Bool) t).fintype
  exact Finite.of_injective
    (fun w : IsingLeapfrogKilledChoiceNoHitAll R t p level =>
      (⟨w.1.1, w.1.2.1⟩ : {bs : List (Bool × Bool) //
        bs.length = t}))
    (by
      intro a b h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg
        (fun z : {bs : List (Bool × Bool) // bs.length = t} => z.1) h)

end
end StatMech.Universality
