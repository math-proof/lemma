/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldTargetReassembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.ABClusterCondition
import Theorem.StatisticalMechanics.Code.Sharpness.ABPhysicalDeriv.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldTargetReassembly
open Finset Set SimpleGraph


namespace StatMech

namespace Sharpness

open ConfigSpace

variable {W : Type*} [Fintype W] [DecidableEq W]

variable (H : SimpleGraph W) [DecidableRel H.Adj]

noncomputable def mtrPhi (p : Sym2 W -> Real) (D : Finset (Sym2 W))
    (o : W) (S : Finset W) : Real :=
  ∑ q ∈ shk_boundaryPairs H S,
    if s(q.1, q.2) ∈ D then
      p s(q.1, q.2) *
        probV p (connEvent H (S : Set W) o {q.1})
    else 0


end Sharpness
end StatMech
