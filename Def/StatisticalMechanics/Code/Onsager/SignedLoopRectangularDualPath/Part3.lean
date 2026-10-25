/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularDualPath.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopDisorderKacWard
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopCriticalWeight
import Structure.StatisticalMechanics.Code.Onsager.SignedLoopRectangularDualPath
open Finset SimpleGraph


namespace StatMech.Onsager

open StatMech.FrontierA StatMech.Sharpness

noncomputable section

def ons_rectDualPathDefect {M N : Nat} (path : ons_RectDualPath M N) :
    Finset (Sym2 (ons_RectDualVertex M N)) :=
  path.walk.edges.toFinset

end
end StatMech.Onsager
