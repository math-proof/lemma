/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonSiteBond.Part2
import Def.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonLaw.Part3
open MeasureTheory
open scoped NNReal


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

variable {d : ℕ}


@[simp] theorem mem_siteCluster {eta : ConfigSpace (Site d)} {x y : Site d} :
    y ∈ siteCluster eta x ↔ (siteOpenGraph eta).Reachable x y :=
  Iff.rfl


end StatMech.FrontierA
