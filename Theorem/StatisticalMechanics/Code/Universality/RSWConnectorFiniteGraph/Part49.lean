module
public import Theorem.StatisticalMechanics.Code.Universality.RSWGapSymmetry.Part4
public import Theorem.StatisticalMechanics.Code.Universality.RSWExtremalTraceContact
public import Theorem.StatisticalMechanics.Code.Universality.RSWExtremalSelectionObstruction
public import Theorem.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part6
public import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
public import Theorem.StatisticalMechanics.Code.FK.OffCentreDomination.Part13
public import Theorem.StatisticalMechanics.Code.FK.WeightedParameterMonotoneClosed
public import Theorem.StatisticalMechanics.Code.FrontierD.FKBoundarySingleMerge
public import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
public import Def.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part67
open Finset SimpleGraph Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_connectorFibreMixtureZ_pos {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    0 < rlc_connectorFibreMixtureZ gamma gamma' p q := by
  unfold rlc_connectorFibreMixtureZ
  apply Finset.sum_pos
  · intro xi _
    exact mul_pos
      (FK.ocd_psiShift_pos
        (Gout := rlc_connectorOuterDualGraph gamma gamma')
        (ιV := rlc_connectorInnerOuterVertex gamma gamma')
        (bdryOut := fun _ => False) hp hp1 hq)
      (FK.activeBCZ_pos
        (rlc_connectorInnerGraph gamma gamma')
        (rlc_connectorInnerInducedWiring gamma gamma'
          (rlc_connectorOuterStateOfSource gamma gamma' xi))
        (fun _ => hp) (fun _ => hp1) hq)
  · exact Finset.univ_nonempty

theorem rlc_connectorFibreWeight_nonneg {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma')) :
    0 ≤ rlc_connectorFibreWeight gamma gamma' p q xi := by
  unfold rlc_connectorFibreWeight
  exact div_nonneg
    (mul_nonneg
      (FK.ocd_psiShift_pos
        (Gout := rlc_connectorOuterDualGraph gamma gamma')
        (ιV := rlc_connectorInnerOuterVertex gamma gamma')
        (bdryOut := fun _ => False) hp hp1 hq).le
      (FK.activeBCZ_pos
        (rlc_connectorInnerGraph gamma gamma')
        (rlc_connectorInnerInducedWiring gamma gamma'
          (rlc_connectorOuterStateOfSource gamma gamma' xi))
        (fun _ => hp) (fun _ => hp1) hq).le)
    (rlc_connectorFibreMixtureZ_pos gamma gamma' hp hp1 hq).le

theorem rlc_connectorFibreWeight_sum_eq_one {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ∑ xi : ConfigSpace (RlcConnectorOuterSourceEdge gamma gamma'),
      rlc_connectorFibreWeight gamma gamma' p q xi = 1 := by
  unfold rlc_connectorFibreWeight rlc_connectorFibreMixtureZ
  rw [← Finset.sum_div]
  exact div_self (rlc_connectorFibreMixtureZ_pos
    gamma gamma' hp hp1 hq).ne'


end
end StatMech.Universality
