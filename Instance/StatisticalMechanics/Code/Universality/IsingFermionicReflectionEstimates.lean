/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflectionEstimates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLineGambler.Part3
import Def.StatisticalMechanics.Code.Universality.IsingFermionicReflectionEstimates.Part2


namespace StatMech.Universality

namespace IsingDiagonalWalkHitSplit

noncomputable instance verticalChoicePathFamily_finite
    (t : Nat) (x y : Int) : Finite (VerticalChoicePathFamily t x y) := by
  letI : Fintype {bs : List Bool // bs.length = t} :=
    (List.finite_length_eq Bool t).fintype
  exact Finite.of_injective
    (fun w : VerticalChoicePathFamily t x y =>
      (⟨w.1, w.2.1⟩ : {bs : List Bool // bs.length = t}))
    (by
      intro a b h
      apply Subtype.ext
      exact congrArg (fun z : {bs : List Bool // bs.length = t} => z.1) h)

end IsingDiagonalWalkHitSplit
end StatMech.Universality
