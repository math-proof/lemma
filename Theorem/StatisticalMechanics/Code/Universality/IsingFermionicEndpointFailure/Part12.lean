/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointFailure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointEscape.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicOrderedEndpointConvolution
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicTailEndpointRace
import Def.StatisticalMechanics.Code.Universality.IsingFermionicEndpointFailure.Part15


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem lineFirstEndpointLeftToNoHit_injective
    (n k : Nat) (start target : IsingLineBox n)
    (hk : 0 < k) (htarget : target.1 = 0) :
    Function.Injective
      (lineFirstEndpointLeftToNoHit n k start target hk htarget) := by
  intro a b hab
  have hword := congrArg
    (fun z : IsingHorizontalNoHitEndpointFamily (k - 1) 0
      (-(start.1 : Int)) => z.1.1) hab
  change a.1.dropLast.reverse = b.1.dropLast.reverse at hword
  have hdrop : a.1.dropLast = b.1.dropLast :=
    List.reverse_injective hword
  apply Subtype.ext
  rw [(lineFirstEndpoint_left_dropLast n k start target a hk htarget).2,
    (lineFirstEndpoint_left_dropLast n k start target b hk htarget).2,
    hdrop]

end
end StatMech.Universality
