/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairLoopFiber.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairCTypeHall.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopVerticalWinding.Part3
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairLoopFiber
open Finset Matrix Polynomial


namespace StatMech.FrontierD

noncomputable section

abbrev SixVertexCompatibleLoopPairing
    {T : EvenTorus} (omega : SixVertexArrows T) :=
  {pairing : FKMedialLoopPairing T //
    forall v, fkLoopPairingCompatible (pairing v) omega v}


end
end StatMech.FrontierD
