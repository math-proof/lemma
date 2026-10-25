/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectQuarterTurn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedSquareReflection.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusCrossingEvents.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKRectQuarterTurn.Part9
open Set SimpleGraph StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

theorem fkRectConnectedWithin_quarterTurn_iff
    (R : FKRectTorus) (hheight : 4 < R.height)
    (omega : R.Configuration) (S : Set R.Vertex) (x y : S) :
    FKRectConnectedWithin (fkRectQuarterTurnTorus R hheight)
        (fkRectQuarterTurnConfigurationEquiv R hheight omega)
        (fkRectQuarterTurnSet R hheight S)
        (fkRectQuarterTurnSetEquiv R hheight S x)
        (fkRectQuarterTurnSetEquiv R hheight S y) ↔
      FKRectConnectedWithin R omega S x y := by
  exact (fkRectOpenGraphQuarterTurnInduceIso
    R hheight omega S).reachable_iff


theorem fkRectCritical_connectedWithinMass_quarterTurn
    (R : FKRectTorus) (hheight : 4 < R.height) (q : Real)
    (S : Set R.Vertex) (x y : S) :
    fkRectCriticalEventMass (fkRectQuarterTurnTorus R hheight) q
        {omega | FKRectConnectedWithin
          (fkRectQuarterTurnTorus R hheight) omega
          (fkRectQuarterTurnSet R hheight S)
          (fkRectQuarterTurnSetEquiv R hheight S x)
          (fkRectQuarterTurnSetEquiv R hheight S y)} =
      fkRectCriticalEventMass R q
        {omega | FKRectConnectedWithin R omega S x y} := by
  classical
  let C := fkRectQuarterTurnConfigurationEquiv R hheight
  let A : Set R.Configuration :=
    {omega | FKRectConnectedWithin R omega S x y}
  let B : Set (fkRectQuarterTurnTorus R hheight).Configuration :=
    {omega | FKRectConnectedWithin
      (fkRectQuarterTurnTorus R hheight) omega
      (fkRectQuarterTurnSet R hheight S)
      (fkRectQuarterTurnSetEquiv R hheight S x)
      (fkRectQuarterTurnSetEquiv R hheight S y)}
  unfold fkRectCriticalEventMass
  rw [← Equiv.sum_comp C (fun eta =>
    B.indicator (fun eta => fkRectCriticalRandomClusterProb
      (fkRectQuarterTurnTorus R hheight) q eta) eta)]
  apply Finset.sum_congr rfl
  intro omega _
  have hmem : C omega ∈ B ↔ omega ∈ A :=
    fkRectConnectedWithin_quarterTurn_iff
      R hheight omega S x y
  have hprob : fkRectCriticalRandomClusterProb
      (fkRectQuarterTurnTorus R hheight) q (C omega) =
        fkRectCriticalRandomClusterProb R q omega :=
    fkRectCriticalRandomClusterProb_quarterTurn
      R hheight q omega
  by_cases hA : omega ∈ A
  · rw [Set.indicator_of_mem hA,
      Set.indicator_of_mem (hmem.mpr hA), hprob]
  · rw [Set.indicator_of_notMem hA,
      Set.indicator_of_notMem (fun hB => hA (hmem.mp hB))]

end
end StatMech.FrontierD
