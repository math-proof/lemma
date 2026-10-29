/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonSingleSiteStability.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonNearestConclusion.Part2
import Def.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonSingleSiteStability
open Set
open scoped NNReal


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.Percolation StatMech.ConfigSpace

variable {d : ℕ}


@[simp] theorem raiseFields_empty (xi : NonnegativeField d) (r : Site d → NNReal) :
    raiseFields xi ∅ r = xi := by
  funext y
  simp [raiseFields]


theorem raiseFields_insert (xi : NonnegativeField d) (S : Finset (Site d))
    (r : Site d → NNReal) {x : Site d} (hx : x ∉ S) :
    raiseFields xi (insert x S) r = raiseField (raiseFields xi S r) x (r x) := by
  funext y
  by_cases hyx : y = x
  · subst y
    simp [raiseFields, raiseField, hx]
  · by_cases hyS : y ∈ S
    · simp [raiseFields, raiseField, hyx, hyS]
    · simp [raiseFields, raiseField, hyx, hyS]


theorem le_raiseFields (xi : NonnegativeField d) (S : Finset (Site d))
    (r : Site d → NNReal) :
    xi ≤ raiseFields xi S r := by
  intro y
  by_cases hy : y ∈ S
  · simp [raiseFields, hy]
  · simp [raiseFields, hy]


theorem raiseFields_mono_set (xi : NonnegativeField d) {S U : Finset (Site d)}
    (hSU : S ⊆ U) (r : Site d → NNReal) :
    raiseFields xi S r ≤ raiseFields xi U r := by
  intro y
  by_cases hyS : y ∈ S
  · have hyU : y ∈ U := hSU hyS
    simp [raiseFields, hyS, hyU]
  · by_cases hyU : y ∈ U
    · simp [raiseFields, hyS, hyU]
    · simp [raiseFields, hyS, hyU]


theorem siteCluster_raiseFields_eq_of_infinite_of_avoids
    (T : MonotoneAutomaton d) (xi : NonnegativeField d)
    (S : Finset (Site d)) (r : Site d → NNReal) (y : Site d)
    (hinf : (siteCluster (T xi) y).Infinite)
    (havoid : ∀ x ∈ S, x ∉ siteCluster (T (raiseFields xi S r)) y) :
    siteCluster (T (raiseFields xi S r)) y = siteCluster (T xi) y := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert x S hx ih =>
      let xiS := raiseFields xi S r
      have hxiSFinal : xiS ≤ raiseFields xi (insert x S) r := by
        exact raiseFields_mono_set xi (Finset.subset_insert x S) r
      have hclusterMono : siteCluster (T xiS) y ⊆
          siteCluster (T (raiseFields xi (insert x S) r)) y := by
        intro z hz
        exact SimpleGraph.Reachable.mono
          (siteOpenGraph_mono (T.monotone hxiSFinal)) hz
      have havoidS : ∀ z ∈ S, z ∉ siteCluster (T xiS) y := by
        intro z hzS hzCluster
        exact havoid z (Finset.mem_insert_of_mem hzS) (hclusterMono hzCluster)
      have ihEq : siteCluster (T xiS) y = siteCluster (T xi) y :=
        ih havoidS
      have hinfS : (siteCluster (T xiS) y).Infinite := by
        rw [ihEq]
        exact hinf
      have hinfFinal :
          (siteCluster (T (raiseFields xi (insert x S) r)) y).Infinite :=
        hinfS.mono hclusterMono
      have hsingle := siteCluster_raise_eq_of_infinite_of_not_mem
        T xiS x y (r x)
      rw [← raiseFields_insert xi S r hx] at hsingle
      exact (hsingle hinfFinal (havoid x (Finset.mem_insert_self x S))).trans ihEq


end StatMech.FrontierA
