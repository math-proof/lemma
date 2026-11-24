module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Ising.PeierlsContourClose.Part4
public import Theorem.StatisticalMechanics.Code.Ising.PeierlsContourCount
open MeasureTheory Filter Topology Finset SimpleGraph
open scoped BigOperators ENNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsContourCount.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Ising

open StatMech.Lattice

attribute [local instance] Classical.propDecidable

variable {d : ℕ}


noncomputable def pcc_pairCluster (p : Site d) : Finset (Site d) := {origin d, p}


end Ising
end StatMech
