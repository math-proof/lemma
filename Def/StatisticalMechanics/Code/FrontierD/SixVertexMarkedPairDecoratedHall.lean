module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairFractionalTransport.Part3
public import Theorem.StatisticalMechanics.Code.Foundations.FiniteBidegreeHall
public import Instance.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairDecoratedHall
open Finset Matrix Polynomial


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairDecoratedHall.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def sixVertexMarkedPairMultiplicityNat
    {T : EvenTorus} (omega eta : SixVertexArrows T) (k : Nat) : Nat :=
  2 ^ (sixVertexTorusCTypeCount omega +
      sixVertexTorusCTypeCount eta - k) *
    (sixVertexTorusCTypeCount omega +
      sixVertexTorusCTypeCount eta).choose k

end
end StatMech.FrontierD
