/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFixedDiamondRobinConvergence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFullSquareBoundaryProjectionAnalyticCollar
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointRadialPointGreen


namespace StatMech.Universality

open Filter Metric Set

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem tendsto_fixedDiamond_endpointRadialHarmonic :
    Tendsto (fun k =>
      (harmonic (3 * isingFermionicProjectionPolynomialSide k + 1) : Real) /
        (isingFermionicProjectionPolynomialSide k : Real))
      atTop (nhds 0) := by
  let q : Nat -> Nat := fun k =>
    isingFermionicProjectionPolynomialSide k - 1
  have hq : Tendsto q atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    refine ⟨b, fun a hab => ?_⟩
    dsimp [q, isingFermionicProjectionPolynomialSide,
      isingFermionicPolynomialSide]
    have hpow : b + 1 <= (a + 2) ^ 5 := by
      calc
        b + 1 <= a + 1 := Nat.add_le_add_right hab 1
        _ <= a + 2 := by omega
        _ <= (a + 2) ^ 5 := Nat.le_pow (by norm_num)
    omega
  have hcomp := tendsto_endpointRadialHarmonic_div_natCast_succ.comp hq
  convert hcomp using 1
  funext k
  have hpos : 0 < isingFermionicProjectionPolynomialSide k :=
    isingFermionicProjectionPolynomialSide_pos k
  simp only [Function.comp_apply, q, Nat.sub_add_cancel hpos]


theorem fixedDiamond_global_side_traces_inconsistent
    {Phi : Complex -> Complex}
    (hleftTrace : Set.EqOn (fun z => (Phi z).im) (fun _ => 0)
      isingFermionicFixedDiamondLeftSide)
    (hfreeTrace : Set.EqOn (fun z => (Phi z).im) (fun _ => 1)
      isingFermionicFixedDiamondFreeSides) : False := by
  have hleft : (-2 : Complex) ∈ isingFermionicFixedDiamondLeftSide := by
    simp [isingFermionicFixedDiamondLeftSide]
  have hfree : (-2 : Complex) ∈ isingFermionicFixedDiamondFreeSides := by
    simp [isingFermionicFixedDiamondFreeSides]
  exact zero_ne_one ((hleftTrace hleft).symm.trans (hfreeTrace hfree))


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
