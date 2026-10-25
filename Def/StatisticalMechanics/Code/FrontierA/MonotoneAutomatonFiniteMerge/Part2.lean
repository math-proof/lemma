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
import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonFiniteMerge
open MeasureTheory Set
open scoped ENNReal


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

variable {d : ℕ}


def SiteTwoMeetBox (n : ℕ) (k : ℕ∞) : Set (ConfigSpace (Site d)) :=
  siteToBond ⁻¹' twoMeetBox d n k


end StatMech.FrontierA
