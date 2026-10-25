/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointEscape.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointRace.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectionEstimates.Part13
import Def.StatisticalMechanics.Code.Universality.IsingFermionicEndpointEscape.Part2


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

noncomputable instance isingLineFarFirstBoundaryFamily_finite (m k : Nat) :
    Finite (IsingLineFarFirstBoundaryFamily m k) := by
  letI : Fintype {ys : List Bool // ys.length = k} :=
    (List.finite_length_eq Bool k).fintype
  exact Finite.of_injective
    (fun w : IsingLineFarFirstBoundaryFamily m k =>
      (⟨w.1, w.2.1⟩ : {ys : List Bool // ys.length = k}))
    (by
      intro a b h
      apply Subtype.ext
      exact congrArg
        (fun z : {ys : List Bool // ys.length = k} => z.1) h)

end
end StatMech.Universality
