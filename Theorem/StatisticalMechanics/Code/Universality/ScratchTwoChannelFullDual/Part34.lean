/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Instance.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part15
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_twoChannelFullInnerMaxSupportedWiring_le_traceKernel {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    rlc_twoChannelFullInnerMaxSupportedWiring gamma gamma' ≤
      rlc_twoChannelFullMaxTraceKernelWiring gamma gamma' := by
  intro x y hxy
  exact ⟨hxy.1, congrArg
    (rlc_twoChannelFullMaxComponentTraceRep gamma gamma')
    (rlc_twoChannelFullMaxInnerContraction_eq_of_maxWiring
      gamma gamma' hxy)⟩


theorem rlc_twoChannelFullIndexed_innerEvent_eq_induced {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (psi : ConfigSpace
      (Sym2 (RlcTwoChannelIndexedOuterVertex gamma gamma')))
    (A : Set (ConfigSpace
      (Sym2 (RlcTwoChannelFullInnerVertex gamma gamma')))) :
    (∑ rho,
        (FK.ocd_innerRestrict
          (rlc_twoChannelFullInnerOuterVertex gamma gamma') ⁻¹' A).indicator
            (fun _ => (1 : Real)) rho *
          FK.condBcProb (rlc_twoChannelIndexedOuterGraph gamma gamma')
            (Lattice.boundaryCliqueGraph (fun _ => False)) p q
            (FK.ocd_innerEdgeFinset
              (rlc_twoChannelFullInnerOuterVertex gamma gamma')) psi rho) =
      ∑ eta,
        A.indicator (fun _ => (1 : Real)) eta *
          FK.bcProb (rlc_twoChannelFullInnerGraph gamma gamma')
            (rlc_twoChannelFullInnerInducedWiring gamma gamma' psi)
            p q eta := by
  rw [FK.ocd_condBcProb_psiExt_sum_eq_inducedBox
    (rlc_twoChannelFullInnerOuterVertex_injective gamma gamma')
    (rlc_twoChannelFullInnerOuter_adjMatch gamma gamma')
    hp hp1 hq psi
    (FK.ocd_innerRestrict
      (rlc_twoChannelFullInnerOuterVertex gamma gamma') ⁻¹' A)]
  have hpre : FK.ocd_psiExt
      (rlc_twoChannelFullInnerOuterVertex gamma gamma') psi ⁻¹'
      (FK.ocd_innerRestrict
        (rlc_twoChannelFullInnerOuterVertex gamma gamma') ⁻¹' A) = A := by
    ext eta
    simp only [Set.mem_preimage,
      FK.ocd_innerRestrict_psiExt
        (rlc_twoChannelFullInnerOuterVertex_injective gamma gamma')]
  rw [hpre]
  rfl


theorem rlc_twoChannelFullIndexed_actualInnerEvent_le_maxSupported
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
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
              (rlc_twoChannelFullInnerOuterVertex gamma gamma'))
            (rlc_twoChannelFullIndexedOuterState gamma gamma' omega) rho) ≤
      FK.bcEventMass (rlc_twoChannelFullInnerGraph gamma gamma')
        (rlc_twoChannelFullInnerMaxSupportedWiring gamma gamma') p q A := by
  rw [rlc_twoChannelFullIndexed_innerEvent_eq_induced
    gamma gamma' hp hp1 (zero_lt_one.trans_le hq)
      (rlc_twoChannelFullIndexedOuterState gamma gamma' omega) A]
  exact FK.bcProb_mono_bc (rlc_twoChannelFullInnerGraph gamma gamma')
    (rlc_twoChannelFullInnerInducedWiring gamma gamma'
      (rlc_twoChannelFullIndexedOuterState gamma gamma' omega))
    (rlc_twoChannelFullInnerMaxSupportedWiring gamma gamma')
    (rlc_twoChannelFullInnerInducedWiring_le_maxSupported
      gamma gamma' omega) hp hp1 hq hA


end
end StatMech.Universality
