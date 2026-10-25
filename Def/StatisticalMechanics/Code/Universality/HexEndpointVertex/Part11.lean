/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointWalk.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexCyclicVertexPartition.Part9
import Theorem.StatisticalMechanics.Code.Universality.HexReturnUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexStripBandClose.Part7
import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part18
import Inductive.StatisticalMechanics.Code.Universality.HexEndpointVertex


namespace StatMech.Universality

open Complex Function HexWalk

open scoped BigOperators

noncomputable section

def HexEndpointLocalAtom.piece
    {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ} :
    HexEndpointLocalAtom region a h0 v du → Finset (List ℤ)
  | .triplet C => C.piece
  | .pair P => P.piece

end
end StatMech.Universality
