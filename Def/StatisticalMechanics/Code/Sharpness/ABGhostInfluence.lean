/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABGhostInfluence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.ABFieldDeriv.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
open Finset Set SimpleGraph


namespace StatMech

namespace Sharpness

open ConfigSpace

open RandomCurrent

variable {E : Type*} [Fintype E] [DecidableEq E]


def abgiClosedPivotal (e : E) (A : Set (ConfigSpace E)) : Set (ConfigSpace E) :=
  {omega | IsPivotal e A omega ∧ omega e = false}


end Sharpness
end StatMech
