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
import Def.StatisticalMechanics.Code.FrontierA.LeeYangRealAnchor.Part2
open Filter Set Topology


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Sharpness StatMech.FK StatMech.Lattice


theorem isingBoxPressureSeq_hasDerivAt_field
    (d n : ℕ) (beta h : ℝ) :
    HasDerivAt (fun x => isingBoxPressureSeq d beta x n)
      (isingBoxPressureFieldDerivative d n beta h) h := by
  let G := boxGraph d n
  have hZ := hasDerivAt_isingZ G beta h
  have hlog := hZ.log (isingZ_ne_zero G beta h)
  have hdiv := hlog.div_const (Fintype.card (boxVerts d n) : ℝ)
  have hexpect := expectation_eq_div G beta h (fun s => ∑ v, spin s v)
  convert hdiv using 1
  unfold isingBoxPressureFieldDerivative
  rw [hexpect]
  have hsum :
      (∑ s : ConfigSpace (boxVerts d n),
        isingWeight G beta h s * (beta * ∑ x, spin s x)) =
        beta * ∑ s : ConfigSpace (boxVerts d n),
          (∑ x, spin s x) * isingWeight G beta h s := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    ring
  rw [hsum]
  ring


theorem leeYangNormalizedFieldLogDerivative_real_eq_pressureDerivative
    (d n : ℕ) (beta h : ℝ) :
    leeYangNormalizedFieldLogDerivative (boxGraph d n) beta (h : ℂ) =
      (isingBoxPressureFieldDerivative d n beta h : ℂ) := by
  rw [leeYangNormalizedFieldLogDerivative_ofReal]
  unfold isingBoxPressureFieldDerivative
  push_cast
  rfl


theorem isingBoxPressureLimit_convexOn_field
    (d : ℕ) (hd : 1 ≤ d) (beta : ℝ) :
    ConvexOn ℝ univ (isingBoxPressureLimit d hd beta) :=
  cdl_limit_convexOn
    (fun n h => isingBoxPressureSeq d beta h n)
    (isingBoxPressureLimit d hd beta)
    (fun n => isingBoxPressureSeq_convexOn_field d n beta)
    (fun h => isingBoxPressure_tendsto_limit d hd beta h)


end StatMech.FrontierA
