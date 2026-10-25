/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheAnisotropyRoots.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFiniteRoots.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheAnisotropyRoots.Part3
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem tendsto_sixVertexHalfFilledBetheRootError
    (k : Nat) (j l : Fin ((k + 1) + (k + 1))) :
    Tendsto (sixVertexHalfFilledBetheRootError k j l) atTop (nhds 0) := by
  exact tendsto_sixVertexTheta_sub_linear_atTop
    (sixVertexHalfFilledBetheRootAt k j)
    (sixVertexHalfFilledBetheRootAt k l)

theorem tendsto_sixVertexHalfFilledBetheRootError_sum
    (k : Nat) (j : Fin ((k + 1) + (k + 1))) :
    Tendsto (fun c => ∑ l, sixVertexHalfFilledBetheRootError k j l c)
      atTop (nhds 0) := by
  simpa using tendsto_finsetSum Finset.univ
    (fun l _ => tendsto_sixVertexHalfFilledBetheRootError k j l)

theorem sixVertexHalfFilledBetheRootAt_eq_quantum_sub_error
    {c : Real} (hc : 2 < c) (k : Nat)
    (j : Fin ((k + 1) + (k + 1))) :
    sixVertexHalfFilledBetheRootAt k j c =
      (2 * Real.pi * sixVertexCentralQuantumNumber j -
          ∑ l, sixVertexHalfFilledBetheRootError k j l c) /
        (((k + 1) + (k + 1) : Nat) : Real) := by
  have heq := sixVertexHalfFilledBetheRootAt_equation hc k j
  have hsum := sixVertexHalfFilledBetheRootAt_sum_eq_zero hc k
  have hn : (0 : Real) < (((k + 1) + (k + 1) : Nat) : Real) := by positivity
  have herr :
      (∑ l, sixVertexHalfFilledBetheRootError k j l c) =
        (∑ l, sixVertexTheta c
          (sixVertexHalfFilledBetheRootAt k j c)
          (sixVertexHalfFilledBetheRootAt k l c)) +
        (((k + 1) + (k + 1) : Nat) : Real) *
          sixVertexHalfFilledBetheRootAt k j c := by
    unfold sixVertexHalfFilledBetheRootError
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hsum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hwidth :
      (sixVertexFourWidth 0 k : Real) =
        2 * (((k + 1) + (k + 1) : Nat) : Real) := by
    unfold sixVertexFourWidth
    push_cast
    ring
  rw [hwidth] at heq
  rw [herr, eq_div_iff hn.ne']
  linarith [heq]


theorem tendsto_sixVertexHalfFilledBetheRootAt (k : Nat)
    (j : Fin ((k + 1) + (k + 1))) :
    Tendsto (sixVertexHalfFilledBetheRootAt k j) atTop
      (nhds (sixVertexHalfFilledLimitingRoot k j)) := by
  have herror := tendsto_sixVertexHalfFilledBetheRootError_sum k j
  have hformula : (fun c => sixVertexHalfFilledBetheRootAt k j c) =ᶠ[atTop]
      fun c =>
        (2 * Real.pi * sixVertexCentralQuantumNumber j -
            ∑ l, sixVertexHalfFilledBetheRootError k j l c) /
          (((k + 1) + (k + 1) : Nat) : Real) := by
    filter_upwards [eventually_gt_atTop (2 : Real)] with c hc
    exact sixVertexHalfFilledBetheRootAt_eq_quantum_sub_error hc k j
  apply Tendsto.congr' hformula.symm
  simpa [sixVertexHalfFilledLimitingRoot] using
    (tendsto_const_nhds.sub herror).div_const
      ((((k + 1) + (k + 1) : Nat) : Real))


theorem tendsto_sixVertexHalfFilledBethePhaseAt (k : Nat)
    (j : Fin ((k + 1) + (k + 1))) :
    Tendsto
      (fun c => sixVertexBethePhase
        (sixVertexHalfFilledBetheRootAt k j c)) atTop
      (nhds (sixVertexHalfFilledLimitingPhase k j)) := by
  have hcontinuous : Continuous (fun p : Real => sixVertexBethePhase p) := by
    unfold sixVertexBethePhase
    fun_prop
  exact hcontinuous.continuousAt.tendsto.comp
    (tendsto_sixVertexHalfFilledBetheRootAt k j)

end
end StatMech.FrontierD
