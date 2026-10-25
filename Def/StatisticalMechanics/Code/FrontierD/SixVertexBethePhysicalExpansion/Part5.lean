/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalExpansion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalReduction.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalExpansion.Part4
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

def sixVertexBetheIELowerCoefficient {n : Nat} (c : Real)
    (z : Fin (n + 1) -> Complex) (S : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) : Complex :=
  if (finRotate (n + 1)).symm i ∈ S then 1
  else if i ∈ S then 0 else sixVertexBetheL c (z i)


def sixVertexBetheIEUpperCoefficient {n : Nat} (c : Real)
    (z : Fin (n + 1) -> Complex) (S : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) : Complex :=
  if i ∈ S then 1
  else if (finRotate (n + 1)).symm i ∈ S then 0
  else sixVertexBetheM c (z i)


def sixVertexBetheRawIEWordCoefficient {n : Nat} (c : Real)
    (z : Fin (n + 1) -> Complex) (w : Finset (Fin (n + 1))) : Complex := by
  classical
  exact ∑ S ∈ (Finset.univ : Finset (Fin (n + 1))).powerset.filter
      SixVertexBetheNoAdjacent,
    (-1 : Complex) ^ S.card *
      ((∏ i ∈ w, sixVertexBetheIELowerCoefficient c z S i) *
        ∏ i ∈ (Finset.univ \ w),
          sixVertexBetheIEUpperCoefficient c z S i)

end
end StatMech.FrontierD
