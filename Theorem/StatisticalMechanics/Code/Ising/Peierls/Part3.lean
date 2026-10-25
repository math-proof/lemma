/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Peierls.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.Gibbs.Part6
import Theorem.StatisticalMechanics.Code.Ising.InfiniteVolume.Part9
import Def.StatisticalMechanics.Code.Ising.Peierls.Part3
open MeasureTheory Filter Topology Finset
open scoped BigOperators ENNReal


set_option linter.unusedVariables false

set_option linter.style.show false


namespace StatMech

namespace Ising

open StatMech.Lattice

variable {d : ℕ}


lemma origin_mem_box (n : ℕ) : origin d ∈ box d n := fun i => by simp [origin]


lemma continuous_spin_apply (x : Site d) :
    Continuous (fun s : ConfigSpace (Site d) => spin s x) :=
  (continuous_of_discreteTopology (f := fun b : Bool => if b then (1 : ℝ) else -1)).comp
    (continuous_apply x)


end Ising
end StatMech
