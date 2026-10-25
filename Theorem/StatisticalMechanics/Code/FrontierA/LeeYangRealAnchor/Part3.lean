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
import Def.StatisticalMechanics.Code.FrontierA.LeeYangRealAnchor.Part3
open Filter Set Topology


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Sharpness StatMech.FK StatMech.Lattice


theorem leeYangPressureRegularRealSet_countable_compl
    (d : ℕ) (hd : 1 ≤ d) (beta : ℝ) :
    (leeYangPressureRegularRealSet d hd beta)ᶜ.Countable := by
  simpa only [leeYangPressureRegularRealSet, mem_setOf_eq, compl_setOf]
    using cdl_countable_leftDeriv_ne_rightDeriv
      (isingBoxPressureLimit_convexOn_field d hd beta)


theorem isingBoxPressureFieldDerivative_tendsto_of_regular
    (d : ℕ) (hd : 1 ≤ d) (beta h : ℝ)
    (hh : h ∈ leeYangPressureRegularRealSet d hd beta) :
    Tendsto (fun n => isingBoxPressureFieldDerivative d n beta h) atTop
      (nhds (pressureRightDeriv (isingBoxPressureLimit d hd beta) h)) := by
  exact fpd_deriv_interchange_of_differentiable
    (fun n x => isingBoxPressureSeq d beta x n)
    (isingBoxPressureLimit d hd beta)
    (fun n x => isingBoxPressureFieldDerivative d n beta x)
    (fun n => isingBoxPressureSeq_convexOn_field d n beta)
    (fun n x => isingBoxPressureSeq_hasDerivAt_field d n beta x)
    (fun x => isingBoxPressure_tendsto_limit d hd beta x)
    h (isingBoxPressureLimit_convexOn_field d hd beta) hh


theorem leeYangBox_normalizedFieldLogDerivative_tendsto_of_regular
    (d : ℕ) (hd : 1 ≤ d) (beta h : ℝ)
    (hh : h ∈ leeYangPressureRegularRealSet d hd beta) :
    Tendsto
      (fun n => leeYangNormalizedFieldLogDerivative
        (boxGraph d n) beta (h : ℂ))
      atTop
      (nhds (pressureRightDeriv
        (isingBoxPressureLimit d hd beta) h : ℂ)) := by
  have hreal := isingBoxPressureFieldDerivative_tendsto_of_regular
    d hd beta h hh
  have hcomplex := Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
  exact hcomplex.congr' (Eventually.of_forall fun n =>
    (leeYangNormalizedFieldLogDerivative_real_eq_pressureDerivative
      d n beta h).symm)


end StatMech.FrontierA
