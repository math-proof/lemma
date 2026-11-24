module
public import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonInsertion.Part3
public import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneMergeGeom
public import Theorem.StatisticalMechanics.Code.Percolation.OffClusterIndep.Part4
public import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonFiniteMerge
open MeasureTheory Set
open scoped ENNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonFiniteMerge.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

variable {d : ℕ}


def SiteTwoMeetBox (n : ℕ) (k : ℕ∞) : Set (ConfigSpace (Site d)) :=
  siteToBond ⁻¹' twoMeetBox d n k


end StatMech.FrontierA
