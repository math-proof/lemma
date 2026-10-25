/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.Exploration.Part5
import Theorem.StatisticalMechanics.Code.Percolation.OffClusterIndep.Part4
import Theorem.StatisticalMechanics.Code.Percolation.SurfaceReassembly
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.Inequalities.Harris
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.ClosedContourSeparation.Part2
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Universality.CrossingTranslationInvariance.Part3
import Theorem.StatisticalMechanics.Code.Universality.ConnectedRCoastClose.Part13
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part11
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_rightDiagonal_of_three (n : ℤ) (hn : 0 < n) :
    rlc_rightToUpper n ∩ rlc_lowerToRight n ∩
        verticalCrossingEvent 0 (2 * n) (-n) n ⊆ rlc_rightDiagonal n := by
  intro omega homega
  obtain ⟨⟨hupper, hlower⟩, hvertical⟩ := homega
  obtain ⟨xu, yu, _hxu, hyu, hcu⟩ := hupper
  obtain ⟨xl, yl, hxl, _hyl, hcl⟩ := hlower
  obtain ⟨xb, yt, hcv⟩ := hvertical
  have hsep : vsFix_VSeparatesHFixed omega 0 (2 * n) 0 (2 * n) (-n) n :=
    vsFix_arc_sides_imp omega 0 (2 * n) 0 (2 * n) (-n) n
      (StatMech.Lattice.jec_vsFix_arc_sides omega (by omega) (by omega))
  have hmeet : HVMeetProperty omega 0 (2 * n) 0 (2 * n) (-n) n :=
    vsFix_hvMeet omega 0 (2 * n) 0 (2 * n) (-n) n hsep
  have h00 : (0 : ℤ) ≤ 0 := le_rfl
  have h02 : (0 : ℤ) ≤ 2 * n := by omega
  have h22 : (2 * n : ℤ) ≤ 2 * n := le_rfl
  obtain ⟨zu, hzuO, hzuH, hcuzu, hcvzu⟩ :=
    hmeet h00 h02 h22 xu yu hcu xb yt hcv
  obtain ⟨zl, hzlO, hzlH, hclzl, hcvzl⟩ :=
    hmeet h00 h02 h22 xl yl hcl xb yt hcv
  have hzlzu : ConnectedWithin 2 omega (rect 0 (2 * n) (-n) n)
      ⟨zl, hzlH⟩ ⟨zu, hzuH⟩ := by
    simpa only using hcvzl.symm.trans hcvzu
  have hconn : ConnectedWithin 2 omega (rect 0 (2 * n) (-n) n)
      ⟨(xl : Site 2), leftSide_subset xl.2⟩
      ⟨(yu : Site 2), rightSide_subset yu.2⟩ :=
    hclzl.trans (hzlzu.trans (hcuzu.symm.trans hcu))
  exact ⟨xl, yu, hxl, hyu, hconn⟩


end Universality
end StatMech
