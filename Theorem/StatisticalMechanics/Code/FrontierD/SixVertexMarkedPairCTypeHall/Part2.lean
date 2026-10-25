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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairCTypeHall
open Finset Matrix Polynomial


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexMarkedPairMultiplicityNat_eq_of_totalC_eq
    {T : EvenTorus} {left right : Fin (T.width + 1)}
    (pair : SixVertexMarkedSectorConfiguration T left ×
      SixVertexMarkedSectorConfiguration T right)
    (k total : Nat) (htotal : sixVertexConfigurationPairTotalC pair = total) :
    sixVertexMarkedPairMultiplicityNat pair.1.1 pair.2.1 k =
      2 ^ (total - k) * total.choose k := by
  simp only [sixVertexMarkedPairMultiplicityNat,
    sixVertexConfigurationPairTotalC] at htotal ⊢
  rw [htotal]

@[simp] theorem sixVertexMarkedDecoratedPairTotalC_eq_pairTotalC
    {T : EvenTorus} {left right : Fin (T.width + 1)} {k : Nat}
    (pair : SixVertexMarkedDecoratedPair T left right k) :
    sixVertexMarkedDecoratedPairTotalC pair =
      sixVertexConfigurationPairTotalC pair.1 :=
  rfl


end
end StatMech.FrontierD
