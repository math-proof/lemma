/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedTorusBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLocalMarkedDisagreementSwitch
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSectorTransferBridge.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedTorusBridge.Part2
open Finset Matrix Polynomial


namespace StatMech.FrontierD

noncomputable section

theorem eval_sixVertexTorusMarkedSectorPartitionPolynomial
    (T : EvenTorus) (n : Fin (T.width + 1)) (t : Real) :
    eval t (sixVertexTorusMarkedSectorPartitionPolynomial T n) =
      svTorusSectorArrowPartitionSum T n (2 + t) := by
  change (evalRingHom t)
      (sixVertexTorusMarkedSectorPartitionPolynomial T n) = _
  rw [sixVertexTorusMarkedSectorPartitionPolynomial,
    svTorusSectorArrowPartitionSum, map_sum]
  apply Finset.sum_congr rfl
  intro omega homega
  by_cases hsector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n.val
  · simp [hsector, eval_sixVertexTorusMarkedWeight]
  · simp [hsector]


theorem sixVertexTorusMarkedSectorPartitionPolynomial_eq_trace
    (T : EvenTorus) (n : Fin (T.width + 1)) :
    sixVertexTorusMarkedSectorPartitionPolynomial T n =
      sixVertexShiftedSectorTracePolynomial T.width T.height n.val := by
  apply Polynomial.funext
  intro t
  calc
    eval t (sixVertexTorusMarkedSectorPartitionPolynomial T n) =
        svTorusSectorArrowPartitionSum T n (2 + t) :=
      eval_sixVertexTorusMarkedSectorPartitionPolynomial T n t
    _ = Matrix.trace
        (sixVertexSectorTransfer T.width n.val (2 + t) ^ T.height) :=
      svTorusSectorArrowPartitionSum_eq_sectorTrace T n (2 + t)
    _ = eval t
        (sixVertexShiftedSectorTracePolynomial
          T.width T.height n.val) :=
      (eval_sixVertexShiftedSectorTracePolynomial
        T.width T.height n.val t).symm


theorem sixVertexMarkedSectorTraceCoefficient_eq_torus_sum
    (T : EvenTorus) (n : Fin (T.width + 1)) (k : Nat) :
    sixVertexMarkedSectorTraceCoefficient
        T.width T.height n.val k =
      ∑ omega : SixVertexArrows T,
        if sixVertexUpCount
            (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n.val then
          (sixVertexTorusMarkedWeight omega).coeff k
        else 0 := by
  unfold sixVertexMarkedSectorTraceCoefficient
  rw [← sixVertexTorusMarkedSectorPartitionPolynomial_eq_trace T n]
  unfold sixVertexTorusMarkedSectorPartitionPolynomial
  rw [← Polynomial.lcoeff_apply, map_sum]
  simp only [Polynomial.lcoeff_apply]
  apply Finset.sum_congr rfl
  intro omega homega
  by_cases hsector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n.val
  · simp [hsector]
  · simp [hsector]


theorem sixVertexMarkedSectorTraceCoefficient_eq_colored_count
    (T : EvenTorus) (n : Fin (T.width + 1)) (k : Nat) :
    sixVertexMarkedSectorTraceCoefficient
        T.width T.height n.val k =
      ∑ omega : SixVertexArrows T,
        if sixVertexUpCount
            (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n.val then
          if omega.IceRule then
            (2 : Real) ^ (sixVertexTorusCTypeCount omega - k) *
              (sixVertexTorusCTypeCount omega).choose k
          else 0
        else 0 := by
  rw [sixVertexMarkedSectorTraceCoefficient_eq_torus_sum]
  apply Finset.sum_congr rfl
  intro omega homega
  by_cases hsector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n.val
  · simp [hsector, coeff_sixVertexTorusMarkedWeight]
  · simp [hsector]

end
end StatMech.FrontierD
