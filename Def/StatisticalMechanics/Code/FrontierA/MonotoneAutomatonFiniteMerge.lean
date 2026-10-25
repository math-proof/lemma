/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonFiniteMerge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonInsertion.Part3
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneMergeGeom
import Theorem.StatisticalMechanics.Code.Percolation.OffClusterIndep.Part4
open MeasureTheory Set
open scoped ENNReal


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

variable {d : ℕ}


noncomputable def siteForceEdges (n : ℕ) (eta : ConfigSpace (Site d)) :
    Finset (Sym2 (Site d)) :=
  (boxEdges d (n + 1)).filter fun e =>
    siteToBond (forceSitesOccupied (boxFinsetBK d n) eta) e = true


end StatMech.FrontierA
