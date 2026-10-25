/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABClusterCondition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.ABGhostInfluence
import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldPercoInhom.Part5
open Finset Set SimpleGraph


namespace StatMech

namespace Sharpness

open ConfigSpace

variable {W : Type*} [Fintype W] [DecidableEq W]

variable (H : SimpleGraph W) [DecidableRel H.Adj]

noncomputable def abccLaw (p : Sym2 W → ℝ) (e : Sym2 W) (b : Bool) : ℝ :=
  if b then p e else 1 - p e

end Sharpness
end StatMech
