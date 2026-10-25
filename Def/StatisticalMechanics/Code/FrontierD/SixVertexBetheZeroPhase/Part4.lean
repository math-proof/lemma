/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeRoots.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCoordinateBetheOne.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhase.Part4
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexZeroPhaseBetheEigenvalueCandidate
    {n : Nat} (c : Real) (N : Nat) (p : Fin n -> Real) (ell : Fin n) : Complex :=
  (sixVertexZeroPhaseBethePrefactor c N p ell : Complex) *
    ∏ j ∈ (Finset.univ.erase ell),
      sixVertexBetheM c (sixVertexBethePhase (p j))


def SixVertexCoordinateBetheZeroPhaseEigenrelation
    {N n : Nat} (c : Real) (p : Fin n -> Real) (ell : Fin n) : Prop :=
  (sixVertexSectorTransferComplex N n c).mulVec
      (sixVertexCoordinateBetheWave c p) =
    sixVertexZeroPhaseBetheEigenvalueCandidate c N p ell •
      sixVertexCoordinateBetheWave c p


end
end StatMech.FrontierD
