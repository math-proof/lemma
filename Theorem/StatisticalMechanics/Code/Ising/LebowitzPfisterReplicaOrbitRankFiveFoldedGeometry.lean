/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveFoldedGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateResidual.Part3
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveFoldedGeometry
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem card_lpReplicaTripleSeamGhostSource
    (sites : I -> V) (hsite : Function.Injective sites)
    {i j k : I} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (lpReplicaTripleSeamGhostSource sites i j k).card = 8 := by
  have hsij : sites i ≠ sites j := hsite.ne hij
  have hsik : sites i ≠ sites k := hsite.ne hik
  have hsjk : sites j ≠ sites k := hsite.ne hjk
  have hi : ({lpReplicaCurrentLeft sites i} :
      Finset (LPReplicaCurrentVertex V)) ∆
        {lpReplicaCurrentRight sites i} =
      {lpReplicaCurrentLeft sites i, lpReplicaCurrentRight sites i} := by
    rw [Finset.symmDiff_eq_union]
    · rfl
    · simp [lpReplicaCurrentLeft, lpReplicaCurrentRight]
  have hj : ({lpReplicaCurrentLeft sites j} :
      Finset (LPReplicaCurrentVertex V)) ∆
        {lpReplicaCurrentRight sites j} =
      {lpReplicaCurrentLeft sites j, lpReplicaCurrentRight sites j} := by
    rw [Finset.symmDiff_eq_union]
    · rfl
    · simp [lpReplicaCurrentLeft, lpReplicaCurrentRight]
  have hk : ({lpReplicaCurrentLeft sites k} :
      Finset (LPReplicaCurrentVertex V)) ∆
        {lpReplicaCurrentRight sites k} =
      {lpReplicaCurrentLeft sites k, lpReplicaCurrentRight sites k} := by
    rw [Finset.symmDiff_eq_union]
    · rfl
    · simp [lpReplicaCurrentLeft, lpReplicaCurrentRight]
  have hg : ({(lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)} :
      Finset (LPReplicaCurrentVertex V)) ∆ {lpReplicaCurrentGhost1} =
      {(lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V),
        lpReplicaCurrentGhost1} := by
    rw [Finset.symmDiff_eq_union]
    · rfl
    · simp [lpReplicaCurrentGhost0, lpReplicaCurrentGhost1]
  have hdij : Disjoint
      ({lpReplicaCurrentLeft sites i, lpReplicaCurrentRight sites i} :
        Finset (LPReplicaCurrentVertex V))
      {lpReplicaCurrentLeft sites j, lpReplicaCurrentRight sites j} := by
    simp [lpReplicaCurrentLeft, lpReplicaCurrentRight, hsij, hsij.symm]
  have hdijk : Disjoint
      (({lpReplicaCurrentLeft sites i, lpReplicaCurrentRight sites i} :
          Finset (LPReplicaCurrentVertex V)) ∪
        {lpReplicaCurrentLeft sites j, lpReplicaCurrentRight sites j})
      {lpReplicaCurrentLeft sites k, lpReplicaCurrentRight sites k} := by
    simp [lpReplicaCurrentLeft, lpReplicaCurrentRight, hsik, hsik.symm,
      hsjk, hsjk.symm]
  have hdghost : Disjoint
      ((({lpReplicaCurrentLeft sites i, lpReplicaCurrentRight sites i} :
          Finset (LPReplicaCurrentVertex V)) ∪
        {lpReplicaCurrentLeft sites j, lpReplicaCurrentRight sites j}) ∪
        {lpReplicaCurrentLeft sites k, lpReplicaCurrentRight sites k})
      {(lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V),
        lpReplicaCurrentGhost1} := by
    simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
      lpReplicaCurrentGhost0, lpReplicaCurrentGhost1]
  unfold lpReplicaTripleSeamGhostSource lpMatchingSeamSource
    lpMatchingGhostSource
  rw [hi, hj, hk, hg]
  rw [Finset.symmDiff_eq_union hdij,
    Finset.symmDiff_eq_union hdijk,
    Finset.symmDiff_eq_union hdghost]
  simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
    lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
    hsij, hsij.symm, hsik, hsik.symm, hsjk, hsjk.symm]


end
end StatMech.Ising
