/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWFailureComplementaryArcObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWRetainedAnchoredContour.Part4
import Theorem.StatisticalMechanics.Code.Universality.RSWFailureComplementaryArcObstruction
open Function MeasureTheory Set


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

def rlc_stdf_rightWalk :
    ((hypercubicLattice 2).induce (rect 0 4 (-2) 2)).Walk
      rlc_stdf_r0 rlc_stdf_r6 :=
  .cons rlc_stdf_radj01
    (.cons rlc_stdf_radj12
      (.cons rlc_stdf_radj23
        (.cons rlc_stdf_radj34
          (.cons rlc_stdf_radj45
            (.cons rlc_stdf_radj56 .nil)))))


noncomputable def rlc_scaleTwoDoubleFailureRight :
    RlcRightDiagonalPath 2 := by
  let x : leftSide 0 4 (-2) 2 :=
    ⟨(rlc_stdf_r0 : Site 2), by
      simp [rlc_stdf_r0, mem_leftSide, mem_rect]⟩
  let y : rightSide 0 4 (-2) 2 :=
    ⟨(rlc_stdf_r6 : Site 2), by
      simp [rlc_stdf_r6, mem_rightSide, mem_rect]⟩
  let p : RlcCrossingPath 0 4 (-2) 2 :=
    ⟨x, y, rlc_stdf_rightWalk.toPath⟩
  exact ⟨p, by simp [p, x, rlc_stdf_r0, rlc_lowerHalf],
    by simp [p, y, rlc_stdf_r6, rlc_upperHalf]⟩

def rlc_stdf_l0 : rect (-4) 0 (-2) 2 :=
  ⟨![-4, -2], by simp [mem_rect]⟩

def rlc_stdf_l1 : rect (-4) 0 (-2) 2 :=
  ⟨![-3, -2], by simp [mem_rect]⟩

def rlc_stdf_l2 : rect (-4) 0 (-2) 2 :=
  ⟨![-2, -2], by simp [mem_rect]⟩

def rlc_stdf_l3 : rect (-4) 0 (-2) 2 :=
  ⟨![-2, -1], by simp [mem_rect]⟩

def rlc_stdf_l4 : rect (-4) 0 (-2) 2 :=
  ⟨![-2, 0], by simp [mem_rect]⟩

def rlc_stdf_l5 : rect (-4) 0 (-2) 2 :=
  ⟨![-1, 0], by simp [mem_rect]⟩

def rlc_stdf_l6 : rect (-4) 0 (-2) 2 :=
  ⟨![0, 0], by simp [mem_rect]⟩

end Universality
end StatMech
