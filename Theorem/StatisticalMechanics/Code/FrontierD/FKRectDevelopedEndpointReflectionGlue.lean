/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedEndpointReflectionGlue.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedWideEndpoint.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusCrossingEvents.Part3
open Set


namespace StatMech.FrontierD

open StatMech.Lattice

noncomputable section

@[simp] theorem fkRectRowReflection_center
    (R : FKRectTorus) (y : Fin R.height) :
    fkRectRowReflection R y.val y = y := by
  apply Fin.ext
  rw [fkRectRowReflection_val]
  have hsub : 2 * y.val + R.height - y.val = y.val + R.height := by
    omega
  rw [hsub, Nat.add_mod_right, Nat.mod_eq_of_lt y.isLt]

@[simp] theorem fkRectDevelopedReflectionVertexEquiv_center
    (R : FKRectTorus) (v : R.Vertex) :
    fkRectDevelopedReflectionVertexEquiv R v.2.val v = v := by
  apply Prod.ext
  · rfl
  · exact fkRectRowReflection_center R v.2


theorem fkRectOpenGraph_developedReflection_reachable_iff
    (R : FKRectTorus) (center : Nat) (omega : R.Configuration)
    (x y : R.Vertex) :
    (fkRectOpenGraph R
      (fkRectDevelopedReflectionConfigurationEquiv R center omega)).Reachable
        (fkRectDevelopedReflectionVertexEquiv R center x)
        (fkRectDevelopedReflectionVertexEquiv R center y) ↔
      (fkRectOpenGraph R omega).Reachable x y := by
  exact (fkRectOpenGraphDevelopedReflectionIso R center omega).reachable_iff

theorem fkRectDevelopedReflection_mem_connectionEvent_iff
    (R : FKRectTorus) (center : Nat) (omega : R.Configuration)
    (x y : R.Vertex) :
    fkRectDevelopedReflectionConfigurationEquiv R center omega ∈
        fkRectTorusConnectionEvent R
          (fkRectDevelopedReflectionVertexEquiv R center x)
          (fkRectDevelopedReflectionVertexEquiv R center y) ↔
      omega ∈ fkRectTorusConnectionEvent R x y :=
  fkRectOpenGraph_developedReflection_reachable_iff
    R center omega x y


theorem fkRectCritical_connectionMass_developedReflection
    (R : FKRectTorus) (center : Nat) (q : Real) (x y : R.Vertex) :
    fkRectCriticalEventMass R q
        (fkRectTorusConnectionEvent R
          (fkRectDevelopedReflectionVertexEquiv R center x)
          (fkRectDevelopedReflectionVertexEquiv R center y)) =
      fkRectCriticalEventMass R q (fkRectTorusConnectionEvent R x y) := by
  classical
  let C := fkRectDevelopedReflectionConfigurationEquiv R center
  let A := fkRectTorusConnectionEvent R x y
  let B := fkRectTorusConnectionEvent R
    (fkRectDevelopedReflectionVertexEquiv R center x)
    (fkRectDevelopedReflectionVertexEquiv R center y)
  unfold fkRectCriticalEventMass
  rw [← Equiv.sum_comp C (fun eta : R.Configuration =>
    B.indicator (fun eta => fkRectCriticalRandomClusterProb R q eta) eta)]
  apply Finset.sum_congr rfl
  intro omega _
  have hmem : C omega ∈ B ↔ omega ∈ A :=
    fkRectDevelopedReflection_mem_connectionEvent_iff
      R center omega x y
  have hprob : fkRectCriticalRandomClusterProb R q (C omega) =
      fkRectCriticalRandomClusterProb R q omega :=
    fkRectCriticalRandomClusterProb_developedReflection
      R center q omega
  by_cases hA : omega ∈ A
  · rw [Set.indicator_of_mem hA,
      Set.indicator_of_mem (hmem.mpr hA), hprob]
  · rw [Set.indicator_of_notMem hA,
      Set.indicator_of_notMem (fun hB => hA (hmem.mp hB))]


end
end StatMech.FrontierD
