/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part14
import Def.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling.Part8


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

noncomputable instance isingLineFirstBoundaryFamily_finite (m k : Nat) :
    Finite (IsingLineFirstBoundaryFamily m k) := by
  letI : Fintype {ys : List Bool // ys.length = k} :=
    (List.finite_length_eq Bool k).fintype
  exact Finite.of_injective
    (fun w : IsingLineFirstBoundaryFamily m k =>
      (⟨w.1, w.2.1⟩ : {ys : List Bool // ys.length = k}))
    (by
      intro a b h
      apply Subtype.ext
      exact congrArg
        (fun z : {ys : List Bool // ys.length = k} => z.1) h)

end
end StatMech.Universality
