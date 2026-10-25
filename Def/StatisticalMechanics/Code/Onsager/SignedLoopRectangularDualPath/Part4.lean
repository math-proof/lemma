/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularDualPath.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopDisorderKacWard
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopCriticalWeight
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopRectangularDualPath
open Finset SimpleGraph


namespace StatMech.Onsager

open StatMech.FrontierA StatMech.Sharpness

noncomputable section

def ons_rectDualPathDefectWeight {M N : Nat}
    (path : ons_RectDualPath M N) (x : Real)
    (edge : Sym2 (ons_RectDualVertex M N)) : Complex :=
  if edge ∈ ons_rectDualPathDefect path then (x : Complex)⁻¹ else (x : Complex)

end
end StatMech.Onsager
