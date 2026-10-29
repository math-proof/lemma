/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonAbsorptionReduction.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.FiniteEventMultivalued
import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
import Theorem.StatisticalMechanics.Code.Percolation.GridBoxConnected.Part2
open MeasureTheory Set Finset SimpleGraph
open scoped ENNReal NNReal BigOperators


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.Percolation StatMech.ConfigSpace

variable {d : ℕ}


theorem siteCluster_raiseFields_eq_of_final_infinite_of_avoids
    (T : MonotoneAutomaton d) (xi : NonnegativeField d)
    (S : Finset (Site d)) (r : Site d → NNReal) (y : Site d)
    (hinf : (siteCluster (T (raiseFields xi S r)) y).Infinite)
    (havoid : ∀ x ∈ S, x ∉ siteCluster (T (raiseFields xi S r)) y) :
    siteCluster (T (raiseFields xi S r)) y = siteCluster (T xi) y := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert x S hx ih =>
      let xiS := raiseFields xi S r
      have hsingle := siteCluster_raise_eq_of_infinite_of_not_mem
        T xiS x y (r x)
      rw [← raiseFields_insert xi S r hx] at hsingle
      have hfinalIntermediate :
          siteCluster (T (raiseFields xi (insert x S) r)) y =
            siteCluster (T xiS) y :=
        hsingle hinf (havoid x (Finset.mem_insert_self x S))
      have hinfS : (siteCluster (T xiS) y).Infinite := by
        rw [← hfinalIntermediate]
        exact hinf
      have havoidS : ∀ z ∈ S, z ∉ siteCluster (T xiS) y := by
        intro z hzS hz
        exact havoid z (Finset.mem_insert_of_mem hzS)
          (hfinalIntermediate.symm ▸ hz)
      exact hfinalIntermediate.trans (ih hinfS havoidS)


theorem siteCluster_zeroFields_eq_of_final_infinite_of_avoids
    (T : MonotoneAutomaton d) (xi : NonnegativeField d)
    (S : Finset (Site d)) (y : Site d)
    (hinf : (siteCluster (T xi) y).Infinite)
    (havoid : ∀ x ∈ S, x ∉ siteCluster (T xi) y) :
    siteCluster (T (zeroFields xi S)) y = siteCluster (T xi) y := by
  have h := siteCluster_raiseFields_eq_of_final_infinite_of_avoids
    T (zeroFields xi S) S xi y
  rw [raiseFields_zeroFields] at h
  exact (h hinf havoid).symm


end StatMech.FrontierA
