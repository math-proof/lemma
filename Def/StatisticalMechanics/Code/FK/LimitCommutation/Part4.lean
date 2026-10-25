/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/LimitCommutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.MultiEdgeDecay.Part4
import Theorem.StatisticalMechanics.Code.FK.LimitCommutation.Part3
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


noncomputable def lmc_transBoxMassFree (v : Site d) (N : ℕ) (t : Finset (Sym2 (boxVerts d N)))
    (p : ℝ) (m : ℕ) (hNm : N ≤ m) : ℝ :=
  med_multiMassProb (fkProb (fvs_transBoxGraph d m v) p 2)
    ((t.image (innerEdgeLE d hNm)).image (Sym2.map (fvs_transEquiv d m v)))


end FK
end StatMech
