/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedAxisSource.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedEndpointRate.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectQuarterTurn.Part9
open Set


namespace StatMech.FrontierD

noncomputable section

def fkRectReflectedCarrierConnectionEvent
    (R : FKRectTorus) (S : Set R.Vertex) (x y : S) :
    Set R.Configuration :=
  let center := y.1.2.val
  let Sr := fkRectDevelopedReflectionSet R center S
  let xr := fkRectDevelopedReflectionVertexEquiv R center x.1
  {omega | FKRectConnectedWithin R omega (S ∪ Sr)
    ⟨x.1, Or.inl x.2⟩ ⟨xr, Or.inr ⟨x.1, x.2, rfl⟩⟩}


end
end StatMech.FrontierD
