module
public import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopDisorderKacWard
public import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopCriticalWeight
public import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopRectangularDualPath.Part2
open Finset SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularDualPath.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Onsager

open StatMech.FrontierA StatMech.Sharpness

noncomputable section

def ons_rectDualPathDefectKWDet {M N : Nat}
    (embedding : KWStraightLineEmbedding (ons_rectDualGraph M N))
    (path : ons_RectDualPath M N) (x : Real) : Complex :=
  (1 - kwGraphTransition (ons_rectDualGraph M N)
    (ons_rectDualPathDefectWeight path x) embedding.turnPhase).det


def ons_rectDualKWDet {M N : Nat}
    (embedding : KWStraightLineEmbedding (ons_rectDualGraph M N))
    (x : Real) : Complex :=
  (1 - kwGraphTransition (ons_rectDualGraph M N)
    (fun _ => (x : Complex)) embedding.turnPhase).det


end
end StatMech.Onsager
