/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc73seqcompress.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc60reimerinjection.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerStep.Part3
import Mathlib.Combinatorics.SetFamily.Compression.Down
set_option linter.style.longLine false

open Finset


namespace StatMech.Walls

open StatMech

variable {α : Type*} [DecidableEq α]


def rc73_slice0 (i : α) (𝒜 : Finset (Finset α)) : Finset (Finset α) :=
  𝒜.filter (fun s => i ∉ s)


def rc73_slice1 (i : α) (𝒜 : Finset (Finset α)) : Finset (Finset α) :=
  (𝒜.filter (fun s => i ∈ s)).image (fun s => s.erase i)


end StatMech.Walls
