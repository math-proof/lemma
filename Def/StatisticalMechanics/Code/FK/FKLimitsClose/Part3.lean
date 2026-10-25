/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKLimitsClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.OffCentreDomination.Part13
import Theorem.StatisticalMechanics.Code.FK.FKLimitsClose.Part2
open MeasureTheory Filter Topology SimpleGraph Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false


namespace StatMech

namespace FK

open StatMech.IsingFK StatMech.Percolation

variable {d : ℕ}


noncomputable def flc_transEdges (v : Site d) (N : ℕ) (t : Finset (Sym2 (boxVerts d N)))
    (m : ℕ) (hNm : N ≤ m) : Finset (Sym2 (fvs_transBoxVerts d m v)) :=
  (t.image (innerEdgeLE d hNm)).image (Sym2.map (fvs_transEquiv d m v))


end FK
end StatMech
