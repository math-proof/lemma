/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationInvariance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.DensityFiniteToInfinite.Part2
import Theorem.StatisticalMechanics.Code.FK.TranslationInvariance.Part3
open MeasureTheory Filter Topology SimpleGraph Set
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

open StatMech.Lattice

variable {d : ℕ}


structure BoxSym (d : ℕ) where
  
  τ : Site d ≃ Site d
  
  adj : ∀ x y, (hypercubicLattice d).Adj (τ x) (τ y) ↔ (hypercubicLattice d).Adj x y
  
  box_mem : ∀ n x, τ x ∈ box d n ↔ x ∈ box d n


end FK
end StatMech
