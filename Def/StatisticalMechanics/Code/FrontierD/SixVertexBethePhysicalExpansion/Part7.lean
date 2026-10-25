/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalExpansion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalReduction.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalExpansion.Part6
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

def sixVertexBetheWordEdgeBase {n : Nat} (c : Real)
    (z : Fin (n + 1) -> Complex) (w : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) : Complex :=
  if i ∈ w then
    if finRotate (n + 1) i ∈ w then
      sixVertexBetheL c (z (finRotate (n + 1) i))
    else 1
  else if finRotate (n + 1) i ∈ w then
    sixVertexBetheM c (z i) *
      sixVertexBetheL c (z (finRotate (n + 1) i))
  else sixVertexBetheM c (z i)

end
end StatMech.FrontierD
