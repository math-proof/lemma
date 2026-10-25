/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSurfaceBulk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalBoundaryInfluence.Part4
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReflectionGauge
import Def.StatisticalMechanics.Code.FrontierA.IsingCriticalSurfaceBulk.Part3
open Filter MeasureTheory Topology


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Lattice StatMech.ConfigSpace
  StatMech.Sharpness

noncomputable section

theorem replicaBridgeMoment_mul_partition_sq
    {V I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (sites : I -> V)
    (r : Real) :
    replicaBridgeMoment G J hf sites r *
        ZJ G.edgeFinset J hf ^ 2 =
      ∑ a : ConfigSpace V, ∑ b : ConfigSpace V,
        wJ G.edgeFinset J hf a * wJ G.edgeFinset J hf b *
          Real.exp (r * replicaBridgeInteraction sites a b) := by
  unfold replicaBridgeMoment ghsiExp2
  field_simp [(ZJ_pos G.edgeFinset J hf).ne']


theorem oddPrismLowerHalfBridgeSiteMean_eq
    (beta : Real) (n : Nat)
    (q : Fin (2 * n + 1) × Fin (2 * n + 1)) :
    letI : DecidableRel (oddPrismLowerHalfGraph n).Adj := Classical.decRel _
    expJ (oddPrismLowerHalfGraph n).edgeFinset (fun _ => beta)
        (fun v => beta * oddPrismPlusField n v.1)
        (fun sigma => spin sigma (oddPrismLowerHalfBridgeSites n q)) =
      oddPrismLowerHalfSurfaceSpinMeanAt beta n q.1 q.2 := by
  dsimp [oddPrismLowerHalfBridgeSites, oddPrismLowerHalfSurfaceSpinMeanAt,
    oddPrismLowerHalfGraph]
  rfl


theorem oddPrismLowerHalfBridgeFreeEnergy_le_of_variance_order
    (beta : Real) (hbeta : 0 <= beta) (n : Nat)
    (hvar :
      letI : DecidableRel (oddPrismLowerHalfGraph n).Adj := Classical.decRel _
      forall t, 0 <= t ->
        replicaBridgeVariance (oddPrismLowerHalfGraph n)
            (fun _ => beta)
            (fun v => beta * oddPrismPlusField n v.1)
            (oddPrismLowerHalfBridgeSites n) t <=
          replicaBridgeVariance (oddPrismLowerHalfGraph n)
            (fun _ => beta)
            (fun v => beta * oddPrismPlusField n v.1)
            (oddPrismLowerHalfBridgeSites n) (-t)) :
    oddPrismLowerHalfBridgeFreeEnergy beta n <=
      2 * beta *
        ∑ q : Fin (2 * n + 1) × Fin (2 * n + 1),
          oddPrismLowerHalfSurfaceSpinMeanAt beta n q.1 q.2 ^ 2 := by
  letI : DecidableRel (oddPrismLowerHalfGraph n).Adj := Classical.decRel _
  have h := replicaBridgeFreeEnergy_le_of_variance_order
    (oddPrismLowerHalfGraph n) (fun _ => beta)
    (fun v => beta * oddPrismPlusField n v.1)
    (oddPrismLowerHalfBridgeSites n) beta hbeta hvar
  unfold oddPrismLowerHalfBridgeFreeEnergy
  rw [show (∑ q : Fin (2 * n + 1) × Fin (2 * n + 1),
      (expJ (oddPrismLowerHalfGraph n).edgeFinset (fun _ => beta)
        (fun v => beta * oddPrismPlusField n v.1)
        (fun sigma => spin sigma (oddPrismLowerHalfBridgeSites n q))) ^ 2) =
      ∑ q : Fin (2 * n + 1) × Fin (2 * n + 1),
        oddPrismLowerHalfSurfaceSpinMeanAt beta n q.1 q.2 ^ 2 by
    apply Finset.sum_congr rfl
    intro q _
    rw [oddPrismLowerHalfBridgeSiteMean_eq]] at h
  exact h


end
end StatMech.FrontierA
