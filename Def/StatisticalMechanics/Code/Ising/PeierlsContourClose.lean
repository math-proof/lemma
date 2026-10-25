/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsContourClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.PeierlsUncond.Part11
import Theorem.StatisticalMechanics.Code.Ising.PeierlsContourClose
open MeasureTheory Filter Topology Finset SimpleGraph
open scoped BigOperators ENNReal


namespace StatMech

namespace Ising

open StatMech.Lattice

attribute [local instance] Classical.propDecidable

variable {d : ℕ}


noncomputable def originClusterFamily (n : ℕ) : Finset (Finset (Site d)) :=
  (clusterFamily (d := d) n).filter (fun K => origin d ∈ K)

end Ising
end StatMech
