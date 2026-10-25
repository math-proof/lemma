/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWTraceSeparationObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWTraceSeparation.Part3
open Function MeasureTheory Set


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

def tsc_v0 : rect 0 2 (-1) 1 :=
  ⟨![0, -1], by simp [mem_rect]⟩

def tsc_v1 : rect 0 2 (-1) 1 :=
  ⟨![1, -1], by simp [mem_rect]⟩

def tsc_v2 : rect 0 2 (-1) 1 :=
  ⟨![2, -1], by simp [mem_rect]⟩

def tsc_v3 : rect 0 2 (-1) 1 :=
  ⟨![2, 0], by simp [mem_rect]⟩

end Universality
end StatMech
