/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeRoots.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCoordinateBetheOne.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhase.Part3
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexZeroPhaseBethePrefactor
    {n : Nat} (c : Real) (N : Nat) (p : Fin n -> Real) (ell : Fin n) : Real :=
  2 + c ^ 2 * ((N : Real) - 1) +
    c ^ 2 * ∑ j ∈ (Finset.univ.erase ell),
      sixVertexThetaLeftDerivAtZero c (p j)


end
end StatMech.FrontierD
