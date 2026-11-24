module
public import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopDisorderKacWard
public import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopCriticalWeight
public import Def.StatisticalMechanics.Code.Onsager.SignedLoopRectangularDualPath.Part2
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

instance (M N : Nat) : DecidableRel (ons_rectDualGraph M N).Adj :=
  inferInstanceAs (DecidableRel (ons_rectDualAdj M N))


end
end StatMech.Onsager
