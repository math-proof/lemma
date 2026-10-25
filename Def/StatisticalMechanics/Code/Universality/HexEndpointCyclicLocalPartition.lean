/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointCyclicLocalPartition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part8
import Def.StatisticalMechanics.Code.Universality.HexEndpointLocalPartitionClosure
import Inductive.StatisticalMechanics.Code.Universality.HexEndpointCyclicLocalPartition


namespace StatMech.Universality

open Complex HexWalk

open scoped BigOperators

noncomputable section

def HexEndpointCyclicLocalAtom.piece
    {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ} :
    HexEndpointCyclicLocalAtom region a h0 v du → Finset (List ℤ)
  | .triplet C => C.piece
  | .pair P => P.piece

end
end StatMech.Universality
