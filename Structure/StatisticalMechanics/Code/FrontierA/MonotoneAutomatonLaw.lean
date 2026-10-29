/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonSiteBond.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonLaw.Part3
open MeasureTheory
open scoped NNReal


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

variable {d : ℕ}


structure MonotoneAutomaton (d : ℕ) where
  toFun : NonnegativeField d → ConfigSpace (Site d)
  measurable_toFun : Measurable toFun
  equivariant : ∀ (g : Multiplicative (Site d)) (xi : NonnegativeField d),
    toFun (fieldShift g xi) = shift g (toFun xi)
  monotone : Monotone toFun
  threshold : NNReal
  occupationThreshold : ∀ (xi : NonnegativeField d) (x : Site d),
    threshold ≤ xi x → toFun xi x = true
  otherInfiniteClustersStable : ∀ (xi : NonnegativeField d) (x : Site d)
    (r : NNReal) (y : Site d),
    y ∉ siteCluster (toFun (raiseField xi x r)) x →
    (siteCluster (toFun (raiseField xi x r)) y).Infinite →
    (siteCluster (toFun xi) y).Infinite

end StatMech.FrontierA
