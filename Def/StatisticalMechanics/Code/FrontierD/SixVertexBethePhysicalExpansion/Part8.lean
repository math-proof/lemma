/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalExpansion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalReduction.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalExpansion.Part7
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

def sixVertexBetheIEMPart {n : Nat} (c : Real)
    (z : Fin (n + 1) -> Complex) (w S : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) : Complex :=
  if i ∈ w then 1 else if i ∈ S then 1 else sixVertexBetheM c (z i)

def sixVertexBetheIEPrevLPart {n : Nat} (c : Real)
    (z : Fin (n + 1) -> Complex) (w S : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) : Complex :=
  if i ∈ w then
    if (finRotate (n + 1)).symm i ∈ S then 1
    else sixVertexBetheL c (z i)
  else 1

def sixVertexBetheIENextLPart {n : Nat} (c : Real)
    (z : Fin (n + 1) -> Complex) (w S : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) : Complex :=
  if finRotate (n + 1) i ∈ w then
    if i ∈ S then 1
    else sixVertexBetheL c (z (finRotate (n + 1) i))
  else 1

end
end StatMech.FrontierD
