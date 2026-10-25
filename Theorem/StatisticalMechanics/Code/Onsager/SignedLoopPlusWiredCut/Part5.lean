/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusWiredCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopAnchoredCut
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopLowTempPlus.Part3
import Theorem.StatisticalMechanics.Code.Ising.KWGeometricDual.Part22
import Def.StatisticalMechanics.Code.Onsager.SignedLoopPlusWiredCut.Part5
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.FrontierA

noncomputable section

theorem ons_plusLowTempPathNumerator_eq_wired
    (d n : Nat) (beta : Real) {u v : Site d}
    (path : (hypercubicLattice d).Walk u v) :
    ons_plusLowTempPathNumerator d n beta path =
      ons_plusWiredPathNumerator d n beta u v := by
  unfold ons_plusLowTempPathNumerator ons_plusWiredPathNumerator
  calc
    (∑ tau : {x // x ∈ box d n} → Bool,
      ons_plusLowTempPathSign (glue (plusField d) tau) path *
        Real.exp (-2 * beta) ^
          (ons_fvCutEdges (bondFinsetTouch d n)
            (glue (plusField d) tau)).card) =
        ∑ tau : {x // x ∈ box d n} → Bool,
          ons_plusWiredEndpointSign d n (ons_optionAnchoredEquiv tau).1 u v *
            Real.exp (-2 * beta) ^
              (multibondCut (ons_plusWiredBondEnds d n)
                (ons_optionAnchoredEquiv tau).1).card := by
      apply Finset.sum_congr rfl
      intro tau _
      rw [ons_plusWiredEndpointSign_eq_pathSign,
        card_plusWiredCut_eq_fvCutEdges]
    _ = _ := by
      rw [← (ons_optionAnchoredEquiv
        (I := {x // x ∈ box d n})).sum_comp]


theorem integral_plusMeasure_twoPoint_eq_wiredCutRatio
    (d n : Nat) (beta : Real) {u v : Site d}
    (path : (hypercubicLattice d).Walk u v) :
    (∫ config, spin config u * spin config v
        ∂(plusMeasure d n beta 0 : MeasureTheory.Measure
          (ConfigSpace (Site d)))) =
      ons_plusWiredPathNumerator d n beta u v /
        ons_plusWiredContourDenominator d n beta := by
  rw [integral_plusMeasure_twoPoint_eq_lowTempPathRatio d n beta path,
    ons_plusLowTempPathNumerator_eq_wired d n beta path,
    ons_plusLowTempContourDenominator_eq_wired d n beta]

end
end StatMech.Onsager
