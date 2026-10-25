/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedOddCandidateAnisotropy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedEvenCandidateAnisotropy.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhaseSingle.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedOddCandidateAnisotropy
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem tendsto_sixVertexFixedOddChargeBethePrefactorNormalized
    (s k : Nat) :
    Tendsto (sixVertexFixedOddChargeBethePrefactorNormalized s k) atTop
      (nhds (sixVertexFixedChargeBetheComplementCount (2 * s + 1) k)) := by
  let r := 2 * s + 1
  let n := sixVertexFixedChargeBetheParticleCount r k
  let N := sixVertexFourWidth r k
  have hderiv : Tendsto
      (fun c => ∑ j : Fin n,
        sixVertexThetaLeftDerivAtZero c
          (sixVertexFixedChargeBetheRootAt r k j c))
      atTop (nhds (-(n : Real))) := by
    have hsum := tendsto_finsetSum Finset.univ fun j _ =>
      tendsto_sixVertexThetaLeftDerivAtZero_atTop
        (sixVertexFixedChargeBetheRootAt r k j)
    have hconst : (∑ _j : Fin n, (-1 : Real)) = -(n : Real) := by simp
    rw [hconst] at hsum
    exact hsum
  have hbracket : Tendsto
      (fun c => (N : Real) + ∑ j : Fin n,
        sixVertexThetaLeftDerivAtZero c
          (sixVertexFixedChargeBetheRootAt r k j c))
      atTop (nhds (sixVertexFixedChargeBetheComplementCount r k : Real)) := by
    have h := (tendsto_const_nhds : Tendsto
      (fun _ : Real => (N : Real)) atTop (nhds (N : Real))).add hderiv
    convert h using 1
    dsimp [N, n, r]
    rw [sixVertexFixedChargeBetheComplementCount_eq,
      sixVertexFixedChargeBetheParticleCount_eq, sixVertexFourWidth]
    push_cast
    ring
  have hscale : Tendsto (fun c : Real => c ^ 2 / (c ^ 2 - 2))
      atTop (nhds 1) := by
    have hinv : Tendsto (fun c : Real => 2 / (c ^ 2 - 2))
        atTop (nhds 0) :=
      tendsto_sixVertexFixedOddPairScale.const_div_atTop 2
    have h0 := (tendsto_const_nhds : Tendsto
      (fun _ : Real => (1 : Real)) atTop (nhds 1)).add hinv
    have h : Tendsto (fun c : Real => 1 + 2 / (c ^ 2 - 2))
        atTop (nhds 1) := by simpa using h0
    apply h.congr'
    filter_upwards [eventually_gt_atTop (2 : Real)] with c hc
    have hd : c ^ 2 - 2 ≠ 0 := by nlinarith
    field_simp [hd]
    ring
  have hprod : Tendsto
      (fun c => c ^ 2 / (c ^ 2 - 2) *
        ((N : Real) + ∑ j : Fin n,
          sixVertexThetaLeftDerivAtZero c
            (sixVertexFixedChargeBetheRootAt r k j c)))
      atTop (nhds (sixVertexFixedChargeBetheComplementCount
        (2 * s + 1) k : Real)) := by
    simpa [r] using hscale.mul hbracket
  apply hprod.congr'
  filter_upwards [eventually_gt_atTop (2 : Real)] with c hc
  rw [sixVertexFixedOddChargeBethePrefactorNormalized, dif_pos hc]
  rw [sixVertexZeroPhaseBethePrefactor_eq hc _ _ _
    (sixVertexFixedChargeBetheRoots_central_eq_zero_of_odd_charge hc
      ⟨s, by omega⟩ k)]
  simp_rw [sixVertexFixedChargeBetheRootAt_eq hc]
  dsimp [r, n, N]
  ring


end
end StatMech.FrontierD
