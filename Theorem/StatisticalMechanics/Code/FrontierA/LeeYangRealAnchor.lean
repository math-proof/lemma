/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangRealAnchor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangNormalFamilyReduction
import Theorem.StatisticalMechanics.Code.Ising.PressureConvex
import Theorem.StatisticalMechanics.Code.Sharpness.GHSFull.Part3
import Theorem.StatisticalMechanics.Code.FK.FKPressureDeriv.Part4
import Def.StatisticalMechanics.Code.FrontierA.LeeYangRealAnchor
open Filter Set Topology


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Sharpness StatMech.FK StatMech.Lattice


theorem isingBoxPressure_tendsto_limit
    (d : ℕ) (hd : 1 ≤ d) (beta h : ℝ) :
    Tendsto (isingBoxPressureSeq d beta h) atTop
      (nhds (isingBoxPressureLimit d hd beta h)) :=
  Classical.choose_spec (isingBoxPressure_tendsto d hd beta h)


theorem isingBoxPressureSeq_convexOn_field
    (d n : ℕ) (beta : ℝ) :
    ConvexOn ℝ univ (fun h => isingBoxPressureSeq d beta h n) := by
  have hconv := isingLogZ_convexOn_field (boxGraph d n) beta
  have hscale : 0 ≤ (1 / (Fintype.card (boxVerts d n) : ℝ)) := by positivity
  have hscaled := hconv.smul hscale
  refine hscaled.congr ?_
  intro h _
  simp only [isingBoxPressureSeq, isingBoxLogZ, smul_eq_mul]
  ring


end StatMech.FrontierA
