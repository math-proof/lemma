/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc57coarsetrif.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc56menger.Part4
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation


theorem bc57_offAxisLine_no_reachesNbr :
    ¬ bc56_ClusterReachesNbr bc56_offAxisLine (bc56_lp 0) := by
  rintro ⟨a, hadj, hmem, _, _⟩
  exact bc56_offAxisLine_no_originNbr a hadj hmem


end StatMech.Walls
