/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLineGambler.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicWalkReflection.Part17
import Def.StatisticalMechanics.Code.Universality.IsingFermionicLineGambler.Part4


namespace StatMech.Universality

open Finset

noncomputable section

noncomputable instance isingLineChoicePathFamily_finite
    (n t : Nat) (p q : IsingLineBox n) :
    Finite (IsingLineChoicePathFamily n t p q) := by
  letI : Fintype {bs : List Bool // bs.length = t} :=
    (List.finite_length_eq Bool t).fintype
  exact Finite.of_injective
    (fun w : IsingLineChoicePathFamily n t p q =>
      (⟨w.1, w.2.1⟩ : {bs : List Bool // bs.length = t}))
    (by
      intro a b h
      apply Subtype.ext
      exact congrArg
        (fun x : {bs : List Bool // bs.length = t} => x.1) h)

end
end StatMech.Universality
