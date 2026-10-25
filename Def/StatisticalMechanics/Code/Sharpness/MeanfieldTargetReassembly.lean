/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldTargetReassembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.ABClusterCondition
import Theorem.StatisticalMechanics.Code.Sharpness.ABPhysicalDeriv.Part2
open Finset Set SimpleGraph


namespace StatMech

namespace Sharpness

open ConfigSpace

variable {W : Type*} [Fintype W] [DecidableEq W]

variable (H : SimpleGraph W) [DecidableRel H.Adj]

noncomputable def mtrLaw (p : Sym2 W -> Real)
    (e : Sym2 W) (b : Bool) : Real :=
  if b then p e else 1 - p e

end Sharpness
end StatMech
