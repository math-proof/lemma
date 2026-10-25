/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWFailureComplementaryArcObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWRetainedAnchoredContour.Part4
open Function MeasureTheory Set


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

def rlc_stdf_r0 : rect 0 4 (-2) 2 :=
  ⟨![0, -2], by simp [mem_rect]⟩

def rlc_stdf_r1 : rect 0 4 (-2) 2 :=
  ⟨![1, -2], by simp [mem_rect]⟩

def rlc_stdf_r2 : rect 0 4 (-2) 2 :=
  ⟨![1, -1], by simp [mem_rect]⟩

def rlc_stdf_r3 : rect 0 4 (-2) 2 :=
  ⟨![2, -1], by simp [mem_rect]⟩

def rlc_stdf_r4 : rect 0 4 (-2) 2 :=
  ⟨![3, -1], by simp [mem_rect]⟩

def rlc_stdf_r5 : rect 0 4 (-2) 2 :=
  ⟨![4, -1], by simp [mem_rect]⟩

def rlc_stdf_r6 : rect 0 4 (-2) 2 :=
  ⟨![4, 0], by simp [mem_rect]⟩

end Universality
end StatMech
