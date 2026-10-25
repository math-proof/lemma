/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheWordAlgebra.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalReduction
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

def SixVertexPhysicalWordExpansion {N n : Nat} (c : Real)
    (p : Fin (n + 1) -> Real) : Prop :=
  forall x : SixVertexSector N (n + 1),
    (sixVertexSectorTransferComplex N (n + 1) c).mulVec
        (sixVertexCoordinateBetheWave c p) x =
      ∑ w : Finset (Fin (n + 1)),
        ∑ sigma, sixVertexBetheAmplitude c p sigma *
          sixVertexBetheWordCoefficient c
            (fun j => sixVertexBethePhase (p j)) sigma w *
          sixVertexBetheWordMonomial N
            (fun j => sixVertexBethePhase (p j)) sigma
            (sixVertexSectorIntCoordinates x) w


end
end StatMech.FrontierD
