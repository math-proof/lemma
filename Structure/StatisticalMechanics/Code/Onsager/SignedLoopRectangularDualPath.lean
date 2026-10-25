/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularDualPath.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopDisorderKacWard
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopCriticalWeight
import Instance.StatisticalMechanics.Code.Onsager.SignedLoopRectangularDualPath.Part2
open Finset SimpleGraph


namespace StatMech.Onsager

open StatMech.FrontierA StatMech.Sharpness

noncomputable section

structure ons_RectDualPath (M N : Nat) where
  source : ons_RectDualVertex M N
  target : ons_RectDualVertex M N
  source_ne_target : source ≠ target
  walk : (ons_rectDualGraph M N).Walk source target
  isPath : walk.IsPath


end
end StatMech.Onsager
