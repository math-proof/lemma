/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairFractionalTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairSwitchInterface.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairFractionalTransport
open Finset Matrix Polynomial


namespace StatMech.FrontierD

noncomputable section

abbrev SixVertexMarkedPairFractionalTransport
    (T : EvenTorus)
    (lower middle upper : Fin (T.width + 1)) (k : Nat) :=
  FiniteFractionalTransport
    (SixVertexMarkedPairSource T lower upper)
    (SixVertexMarkedPairTarget T middle)
    (fun pair => sixVertexMarkedPairMultiplicity pair.1.1 pair.2.1 k)
    (fun pair => sixVertexMarkedPairMultiplicity pair.1.1 pair.2.1 k)


abbrev SixVertexMarkedPairFractionalTransportOn
    (T : EvenTorus)
    (lower middle upper : Fin (T.width + 1)) (k : Nat)
    (related : SixVertexMarkedPairSource T lower upper ->
      SixVertexMarkedPairTarget T middle -> Prop) :=
  FiniteFractionalTransportOn
    (SixVertexMarkedPairSource T lower upper)
    (SixVertexMarkedPairTarget T middle)
    (fun pair => sixVertexMarkedPairMultiplicity pair.1.1 pair.2.1 k)
    (fun pair => sixVertexMarkedPairMultiplicity pair.1.1 pair.2.1 k)
    related


end
end StatMech.FrontierD
