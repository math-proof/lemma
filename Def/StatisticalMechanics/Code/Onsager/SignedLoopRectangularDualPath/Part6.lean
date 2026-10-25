/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularDualPath.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopDisorderKacWard
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopCriticalWeight
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopRectangularDualPath.Part3
open Finset SimpleGraph


namespace StatMech.Onsager

open StatMech.FrontierA StatMech.Sharpness

noncomputable section

def ons_rectDualPathSignedLoopObservable {M N : Nat}
    (path : ons_RectDualPath M N) (x : Real) : Complex :=
  (ons_sourceX (ons_rectDualGraph M N) {path.source, path.target} x : Complex) ^ 2 /
    (x : Complex) ^ (2 * (ons_rectDualPathDefect path).card)


end
end StatMech.Onsager
