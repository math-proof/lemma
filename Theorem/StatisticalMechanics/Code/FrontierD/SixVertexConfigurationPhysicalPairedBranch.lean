/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPhysicalPairedBranch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FiniteTwoBranchWeightedTransport
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairTotalCMonotone.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalPairedBranch
open Finset Matrix Polynomial


namespace StatMech.FrontierD

noncomputable section

theorem SixVertexArrows.weight_eq_pow_cTypeCount
    {T : EvenTorus} (omega : SixVertexArrows T) (homega : omega.IceRule)
    (c : Real) :
    omega.weight c = c ^ sixVertexTorusCTypeCount omega := by
  have heval := eval_sixVertexTorusMarkedWeight (c - 2) omega
  have hc : 2 + (c - 2) = c := by ring
  rw [hc] at heval
  rw [← heval, sixVertexTorusMarkedWeight_eq_pow omega homega]
  simp

theorem sum_pow_sixVertexMarkedSectorConfiguration_eq_trace
    (T : EvenTorus) (sector : Fin (T.width + 1)) (c : Real) :
    (∑ omega : SixVertexMarkedSectorConfiguration T sector,
      c ^ sixVertexTorusCTypeCount omega.1) =
      Matrix.trace
        (sixVertexSectorTransfer T.width sector.val c ^ T.height) := by
  calc
    (∑ omega : SixVertexMarkedSectorConfiguration T sector,
        c ^ sixVertexTorusCTypeCount omega.1) =
        ∑ omega : SixVertexMarkedSectorConfiguration T sector,
          omega.1.weight c := by
      apply Finset.sum_congr rfl
      intro omega _
      exact (omega.1.weight_eq_pow_cTypeCount omega.2.1 c).symm
    _ = eval (c - 2)
        (sixVertexMarkedSectorConfigurationPolynomial T sector) := by
      unfold sixVertexMarkedSectorConfigurationPolynomial
      change (∑ omega : SixVertexMarkedSectorConfiguration T sector,
        omega.1.weight c) =
          (evalRingHom (c - 2))
            (∑ omega : SixVertexMarkedSectorConfiguration T sector,
              sixVertexTorusMarkedWeight omega.1)
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro omega _
      have heval := eval_sixVertexTorusMarkedWeight (c - 2) omega.1
      have hc : 2 + (c - 2) = c := by ring
      rw [hc] at heval
      exact heval.symm
    _ = eval (c - 2)
        (sixVertexShiftedSectorTracePolynomial
          T.width T.height sector.val) := by
      rw [sixVertexMarkedSectorConfigurationPolynomial_eq_trace]
    _ = Matrix.trace
        (sixVertexSectorTransfer T.width sector.val c ^ T.height) := by
      rw [eval_sixVertexShiftedSectorTracePolynomial]
      congr 3
      ring

theorem sum_pow_configurationPairTotalC_eq_trace_mul_trace
    (T : EvenTorus) (left right : Fin (T.width + 1)) (c : Real) :
    (∑ pair : SixVertexMarkedSectorConfiguration T left ×
        SixVertexMarkedSectorConfiguration T right,
      c ^ sixVertexConfigurationPairTotalCPhysical pair) =
      Matrix.trace (sixVertexSectorTransfer T.width left.val c ^ T.height) *
        Matrix.trace (sixVertexSectorTransfer T.width right.val c ^ T.height) := by
  rw [← sum_pow_sixVertexMarkedSectorConfiguration_eq_trace,
    ← sum_pow_sixVertexMarkedSectorConfiguration_eq_trace]
  simp only [sixVertexConfigurationPairTotalCPhysical, pow_add]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [Fintype.sum_prod_type]


end
end StatMech.FrontierD
