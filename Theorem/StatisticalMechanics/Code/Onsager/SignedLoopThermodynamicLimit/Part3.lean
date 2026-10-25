/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopThermodynamicLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopRectangularDualPath.Part4
import Theorem.StatisticalMechanics.Code.FrontierB.FreeBoxEvenLimit.Part6
import Def.StatisticalMechanics.Code.Onsager.SignedLoopThermodynamicLimit.Part2
open Finset SimpleGraph MeasureTheory Filter Topology


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.Sharpness StatMech.FrontierA
  StatMech.FrontierB

noncomputable section

theorem ons_rectDualPathCriticalRatio_tendsto_freeState
    (embedding : ∀ n, KWStraightLineEmbedding
      (ons_rectDualGraph (2 * n) (2 * n)))
    (path : ∀ n, ons_RectDualPath (2 * n) (2 * n))
    (a b : Site 2)
    (hsource : ∀ᶠ n in atTop,
      ((ons_box2EquivRect n).symm (path n).source).1 = a)
    (htarget : ∀ᶠ n in atTop,
      ((ons_box2EquivRect n).symm (path n).target).1 = b) :
    Tendsto (fun n => ons_rectDualPathCriticalRatio (embedding n) (path n))
      atTop
      (nhds ((((∫ spin, spinProd {a, b} spin
        ∂(freeState 2 ons_betaC 0 : Measure (ConfigSpace (Site 2)))) : Real) :
          Complex) ^ 2)) := by
  let f : Nat -> Real := fun n =>
    ∫ spin, spinProd {a, b} spin
      ∂(freeMeasure 2 n ons_betaC 0 : Measure (ConfigSpace (Site 2)))
  have hf : Tendsto f atTop
      (nhds (∫ spin, spinProd {a, b} spin
        ∂(freeState 2 ons_betaC 0 : Measure (ConfigSpace (Site 2))))) := by
    simpa only [f] using
      integral_freeMeasure_spinProd_tendsto_freeState
        2 ons_betaC ons_betaC_pos.le ({a, b} : Finset (Site 2))
  have hfComplex : Tendsto (fun n => (f n : Complex)) atTop
      (nhds (((∫ spin, spinProd {a, b} spin
        ∂(freeState 2 ons_betaC 0 : Measure (ConfigSpace (Site 2)))) : Real) :
          Complex)) := by
    simpa only [Function.comp_apply] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp hf
  apply (hfComplex.pow 2).congr'
  filter_upwards [hsource, htarget] with n hs ht
  rw [show ons_rectDualPathCriticalRatio (embedding n) (path n) =
      (isingExpectation (ons_rectDualGraph (2 * n) (2 * n)) ons_betaC 0
        (fun spin => Ising.spin spin (path n).source *
          Ising.spin spin (path n).target) : Complex) ^ 2 by
    symm
    exact coe_ons_rectDualPath_criticalTwoPoint_sq_eq_kwDet_ratio
      (embedding n) (path n)]
  rw [show (isingExpectation (ons_rectDualGraph (2 * n) (2 * n))
      ons_betaC 0 (fun spin => Ising.spin spin (path n).source *
        Ising.spin spin (path n).target) : Complex) =
      (((∫ spin, spinProd
        {((ons_box2EquivRect n).symm (path n).source).1,
          ((ons_box2EquivRect n).symm (path n).target).1} spin
        ∂(freeMeasure 2 n ons_betaC 0 : Measure (ConfigSpace (Site 2)))) : Real) :
          Complex) by
    exact_mod_cast ons_rectDualPath_twoPoint_eq_freeMeasure
      n ons_betaC (path n)]
  simp only [hs, ht, f]

end
end StatMech.Onsager
