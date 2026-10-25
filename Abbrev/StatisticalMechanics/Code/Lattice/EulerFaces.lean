/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerFaces.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.Cyclomatic.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces.Part2
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

abbrev boxInduce (n : ℕ) := (hypercubicLattice 2).induce (box 2 n)


end Lattice
end StatMech
