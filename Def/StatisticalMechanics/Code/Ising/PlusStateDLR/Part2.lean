/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateDLR.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GibbsSimplex.Part3
import Theorem.StatisticalMechanics.Code.Ising.GibbsExtreme
import Theorem.StatisticalMechanics.Code.Ising.PlusStateDLR
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology
open scoped BigOperators ENNReal NNReal BoundedContinuousFunction

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.Lattice

variable {d : ℕ}


noncomputable def specApply_bcf (n : ℕ) (B : Finset (Sym2 (Site d))) (β h : ℝ)
    (f : ConfigSpace (Site d) →ᵇ ℝ) : ConfigSpace (Site d) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨specApply n B β h (f : ConfigSpace (Site d) → ℝ), specApply_continuous n B β h f.continuous⟩

end Ising
end StatMech
