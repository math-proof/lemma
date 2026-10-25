/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairCTypeHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairDecoratedHall.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairReconnectionWitness
import Mathlib.Data.Fintype.EquivFin
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairCTypeHall.Part2
open Finset Matrix Polynomial


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexMarkedDecoratedPairTotalCFiberEquiv
    (T : EvenTorus) (left right : Fin (T.width + 1)) (k total : Nat) :
    {decorated : SixVertexMarkedDecoratedPair T left right k //
        sixVertexMarkedDecoratedPairTotalC decorated = total} ≃
      ({pair : SixVertexMarkedSectorConfiguration T left ×
          SixVertexMarkedSectorConfiguration T right //
          sixVertexConfigurationPairTotalC pair = total} ×
        Fin (2 ^ (total - k) * total.choose k)) where
  toFun decorated :=
    ⟨⟨decorated.1.1, decorated.2⟩,
      Fin.cast
        (sixVertexMarkedPairMultiplicityNat_eq_of_totalC_eq
          decorated.1.1 k total decorated.2)
        decorated.1.2⟩
  invFun decorated :=
    ⟨⟨decorated.1.1,
        Fin.cast
          (sixVertexMarkedPairMultiplicityNat_eq_of_totalC_eq
            decorated.1.1 k total decorated.1.2).symm
          decorated.2⟩,
      decorated.1.2⟩
  left_inv decorated := by
    apply Subtype.ext
    apply Sigma.ext
    · rfl
    · simp
  right_inv decorated := by
    apply Prod.ext
    · rfl
    · simp

end
end StatMech.FrontierD
