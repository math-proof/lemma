/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part14
import Def.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling.Part10


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

noncomputable instance isingLineBoundaryStringFamily_finite (m K : Nat) :
    Finite (IsingLineBoundaryStringFamily m K) := by
  letI : Fintype {ys : List Bool // ys.length = K} :=
    (List.finite_length_eq Bool K).fintype
  exact Finite.of_injective
    (fun w : IsingLineBoundaryStringFamily m K =>
      (⟨w.1, w.2.1⟩ : {ys : List Bool // ys.length = K}))
    (by
      intro a b h
      apply Subtype.ext
      exact congrArg
        (fun z : {ys : List Bool // ys.length = K} => z.1) h)

end
end StatMech.Universality
