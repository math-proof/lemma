/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonSingleSiteStability.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonNearestConclusion.Part2
import Def.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonSingleSiteStability.Part2
open Set
open scoped NNReal


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.Percolation StatMech.ConfigSpace

variable {d : ℕ}


theorem raiseFields_zeroFields (xi : NonnegativeField d) (S : Finset (Site d)) :
    raiseFields (zeroFields xi S) S xi = xi := by
  funext y
  by_cases hy : y ∈ S
  · simp [raiseFields, zeroFields, hy]
  · simp [raiseFields, zeroFields, hy]


theorem siteCluster_zeroFields_eq_of_infinite_of_avoids
    (T : MonotoneAutomaton d) (xi : NonnegativeField d)
    (S : Finset (Site d)) (y : Site d)
    (hinf : (siteCluster (T (zeroFields xi S)) y).Infinite)
    (havoid : ∀ x ∈ S, x ∉ siteCluster (T xi) y) :
    siteCluster (T (zeroFields xi S)) y = siteCluster (T xi) y := by
  have h := siteCluster_raiseFields_eq_of_infinite_of_avoids
    T (zeroFields xi S) S xi y hinf
  rw [raiseFields_zeroFields] at h
  exact (h havoid).symm

end StatMech.FrontierA
