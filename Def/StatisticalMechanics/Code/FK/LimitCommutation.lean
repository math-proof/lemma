/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/LimitCommutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.MultiEdgeDecay.Part4
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


noncomputable def lmc_transEdgeIncl (d m : ℕ) (v : Site d) :
    Sym2 (fvs_transBoxVerts d m v) → Sym2 (Site d) :=
  Sym2.map (Subtype.val : fvs_transBoxVerts d m v → Site d)


end FK
end StatMech
