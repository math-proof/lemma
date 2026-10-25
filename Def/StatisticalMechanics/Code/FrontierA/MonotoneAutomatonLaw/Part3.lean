/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonSiteBond.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonLaw.Part2
open MeasureTheory
open scoped NNReal


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

variable {d : ℕ}


def siteCluster (eta : ConfigSpace (Site d)) (x : Site d) : Set (Site d) :=
  {y | (siteOpenGraph eta).Reachable x y}

end StatMech.FrontierA
