/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointRace.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLocalBallot.Part5
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFourthMoment
import Def.StatisticalMechanics.Code.Universality.IsingFermionicEndpointRace.Part3


namespace StatMech.Universality

open Finset

noncomputable section

noncomputable instance endpointBoundaryStringFamily_finite (m K : Nat) :
    Finite (EndpointBoundaryStringFamily m K) := by
  letI : Fintype {ys : List Bool // ys.length = K} :=
    (List.finite_length_eq Bool K).fintype
  exact Finite.of_injective
    (fun w : EndpointBoundaryStringFamily m K =>
      (⟨w.1, w.2.1⟩ : {ys : List Bool // ys.length = K}))
    (by
      intro a b h
      apply Subtype.ext
      exact congrArg
        (fun z : {ys : List Bool // ys.length = K} => z.1) h)

end
end StatMech.Universality
