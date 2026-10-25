/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part43
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_twoChannelFullIndexed_actualConnectorFibreMass_le_maxSupported
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    rlc_twoChannelFullIndexed_actualConnectorFibreMass
        gamma gamma' p q omega ≤
      FK.bcEventMass (rlc_twoChannelFullInnerGraph gamma gamma')
        (rlc_twoChannelFullInnerMaxSupportedWiring gamma gamma') p q
        (rlc_twoChannelFullInnerExteriorEvent gamma gamma') := by
  unfold rlc_twoChannelFullIndexed_actualConnectorFibreMass
  exact rlc_twoChannelFullIndexed_actualInnerEvent_le_maxSupported
    gamma gamma' hp hp1 hq omega
    (rlc_twoChannelFullInnerExteriorEvent gamma gamma')
    (rlc_twoChannelFullInnerExteriorEvent_isIncreasing gamma gamma')


theorem rlc_twoChannelFullIndexed_actualConnectorMixture_le_maxSupported
    {n : Int} {I : Type*} [Fintype I] [DecidableEq I]
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (weight : I → Real) (hweight : ∀ i, 0 ≤ weight i)
    (hweightSum : ∑ i, weight i = 1)
    (omega : I → RlcTwoChannelEdgeConfig gamma gamma') :
    (∑ i, weight i *
      rlc_twoChannelFullIndexed_actualConnectorFibreMass
        gamma gamma' p q (omega i)) ≤
      FK.bcEventMass (rlc_twoChannelFullInnerGraph gamma gamma')
        (rlc_twoChannelFullInnerMaxSupportedWiring gamma gamma') p q
        (rlc_twoChannelFullInnerExteriorEvent gamma gamma') := by
  let target := FK.bcEventMass
    (rlc_twoChannelFullInnerGraph gamma gamma')
    (rlc_twoChannelFullInnerMaxSupportedWiring gamma gamma') p q
    (rlc_twoChannelFullInnerExteriorEvent gamma gamma')
  calc
    (∑ i, weight i *
      rlc_twoChannelFullIndexed_actualConnectorFibreMass
        gamma gamma' p q (omega i)) ≤
        ∑ i, weight i * target := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left
        (rlc_twoChannelFullIndexed_actualConnectorFibreMass_le_maxSupported
          gamma gamma' hp hp1 hq (omega i)) (hweight i)
    _ = target := by rw [← Finset.sum_mul, hweightSum, one_mul]


theorem rlc_twoChannelFullIndexed_innerEvent_le_merged {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (psi : ConfigSpace
      (Sym2 (RlcTwoChannelIndexedOuterVertex gamma gamma')))
    (hwire : rlc_twoChannelFullInnerInducedWiring gamma gamma' psi ≤
      rlc_twoChannelFullInnerMergedWiring gamma gamma')
    (A : Set (ConfigSpace
      (Sym2 (RlcTwoChannelFullInnerVertex gamma gamma'))))
    (hA : IsIncreasing A) :
    (∑ rho,
        (FK.ocd_innerRestrict
          (rlc_twoChannelFullInnerOuterVertex gamma gamma') ⁻¹' A).indicator
            (fun _ => (1 : Real)) rho *
          FK.condBcProb (rlc_twoChannelIndexedOuterGraph gamma gamma')
            (Lattice.boundaryCliqueGraph (fun _ => False)) p q
            (FK.ocd_innerEdgeFinset
              (rlc_twoChannelFullInnerOuterVertex gamma gamma')) psi rho) ≤
      FK.bcEventMass (rlc_twoChannelFullInnerGraph gamma gamma')
        (rlc_twoChannelFullInnerMergedWiring gamma gamma') p q A := by
  rw [rlc_twoChannelFullIndexed_innerEvent_eq_induced
    gamma gamma' hp hp1 (zero_lt_one.trans_le hq) psi A]
  exact FK.bcProb_mono_bc (rlc_twoChannelFullInnerGraph gamma gamma')
    (rlc_twoChannelFullInnerInducedWiring gamma gamma' psi)
    (rlc_twoChannelFullInnerMergedWiring gamma gamma')
    hwire hp hp1 hq hA


theorem rlc_twoChannelFullIndexed_innerEvent_half_q_one_eq_merged {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (psi : ConfigSpace
      (Sym2 (RlcTwoChannelIndexedOuterVertex gamma gamma')))
    (A : Set (ConfigSpace
      (Sym2 (RlcTwoChannelFullInnerVertex gamma gamma')))) :
    (∑ rho,
        (FK.ocd_innerRestrict
          (rlc_twoChannelFullInnerOuterVertex gamma gamma') ⁻¹' A).indicator
            (fun _ => (1 : Real)) rho *
          FK.condBcProb (rlc_twoChannelIndexedOuterGraph gamma gamma')
            (Lattice.boundaryCliqueGraph (fun _ => False)) (1 / 2) 1
            (FK.ocd_innerEdgeFinset
              (rlc_twoChannelFullInnerOuterVertex gamma gamma')) psi rho) =
      FK.bcEventMass (rlc_twoChannelFullInnerGraph gamma gamma')
        (rlc_twoChannelFullInnerMergedWiring gamma gamma')
        (1 / 2) 1 A := by
  rw [rlc_twoChannelFullIndexed_innerEvent_eq_induced
    gamma gamma' (by norm_num) (by norm_num) (by norm_num) psi A]
  unfold FK.bcEventMass
  apply Finset.sum_congr rfl
  intro eta _
  congr 1
  exact rlc_bcProb_half_q_one_uniform
    (rlc_twoChannelFullInnerGraph gamma gamma')
    (rlc_twoChannelFullInnerInducedWiring gamma gamma' psi)
    (rlc_twoChannelFullInnerMergedWiring gamma gamma') eta eta


theorem rlc_twoChannelFullIndexed_fibreMixture_half_q_one_eq_merged
    {n : Int} {I : Type*} [Fintype I] [DecidableEq I]
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (weight : I → Real)
    (psi : I → ConfigSpace
      (Sym2 (RlcTwoChannelIndexedOuterVertex gamma gamma')))
    (hweight : ∑ i, weight i = 1)
    (A : Set (ConfigSpace
      (Sym2 (RlcTwoChannelFullInnerVertex gamma gamma')))) :
    (∑ i, weight i *
      (∑ rho,
        (FK.ocd_innerRestrict
          (rlc_twoChannelFullInnerOuterVertex gamma gamma') ⁻¹' A).indicator
            (fun _ => (1 : Real)) rho *
          FK.condBcProb (rlc_twoChannelIndexedOuterGraph gamma gamma')
            (Lattice.boundaryCliqueGraph (fun _ => False)) (1 / 2) 1
            (FK.ocd_innerEdgeFinset
              (rlc_twoChannelFullInnerOuterVertex gamma gamma'))
            (psi i) rho)) =
      FK.bcEventMass (rlc_twoChannelFullInnerGraph gamma gamma')
        (rlc_twoChannelFullInnerMergedWiring gamma gamma')
        (1 / 2) 1 A := by
  simp_rw [rlc_twoChannelFullIndexed_innerEvent_half_q_one_eq_merged
    gamma gamma' _ A]
  rw [← Finset.sum_mul, hweight, one_mul]


end
end StatMech.Universality
