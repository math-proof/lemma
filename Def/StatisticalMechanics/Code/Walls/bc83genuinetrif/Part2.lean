/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc83genuinetrif.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc81gncutae
import Theorem.StatisticalMechanics.Code.Walls.bc78mergedichotomy
import Theorem.StatisticalMechanics.Code.Walls.bc73sublattice.Part5
import Theorem.StatisticalMechanics.Code.Walls.bc83genuinetrif
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


noncomputable def bc83_genuineTrifFinset (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) :
    Finset (Site d) := by
  classical
  exact (boxFinsetBK d R).filter (fun y => bc83_genuineTrif ω L y)


noncomputable def bc83_genuineTrifCount (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) : ℕ :=
  (bc83_genuineTrifFinset ω L R).card


end StatMech.Walls
