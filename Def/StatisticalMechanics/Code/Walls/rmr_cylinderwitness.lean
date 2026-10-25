/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_cylinderwitness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.PerOrbitCardClose.Part8
open Finset


namespace StatMech.Walls

open StatMech ConfigSpace

variable {E : Type*}


def cylinder (K : Finset E) (ω : ConfigSpace E) : Set (ConfigSpace E) :=
  {ω' | agreeOn (↑K) ω ω'}

end StatMech.Walls
