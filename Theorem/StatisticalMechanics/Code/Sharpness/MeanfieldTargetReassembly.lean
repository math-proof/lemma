/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldTargetReassembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.ABClusterCondition
import Theorem.StatisticalMechanics.Code.Sharpness.ABPhysicalDeriv.Part2
import Def.StatisticalMechanics.Code.Sharpness.MeanfieldTargetReassembly
open Finset Set SimpleGraph


namespace StatMech

namespace Sharpness

open ConfigSpace

variable {W : Type*} [Fintype W] [DecidableEq W]

variable (H : SimpleGraph W) [DecidableRel H.Adj]

theorem mtrLaw_sum_one (p : Sym2 W -> Real) (e : Sym2 W) :
    mtrLaw p e false + mtrLaw p e true = 1 := by
  simp [mtrLaw]

theorem mtr_probV_eq_wprob (p : Sym2 W -> Real)
    (A : Set (ConfigSpace (Sym2 W))) :
    probV p A = wprob (mtrLaw p) A := by
  unfold probV wprob configWeightV pweight edgeWeightV mtrLaw
  rfl


end Sharpness
end StatMech
