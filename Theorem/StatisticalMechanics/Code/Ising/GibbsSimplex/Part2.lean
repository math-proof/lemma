/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsSimplex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Ising.DLR
import Def.StatisticalMechanics.Code.Ising.GibbsSimplex.Part2
open MeasureTheory ProbabilityTheory MeasurableSpace Set
open scoped BigOperators ENNReal

set_option linter.style.longLine false


namespace StatMech

namespace Ising

open StatMech.Lattice

variable {d : ℕ}


@[simp] theorem isingSpec_apply (n : ℕ) (B : Finset (Sym2 (Site d))) (β h : ℝ)
    (η : ConfigSpace (Site d)) :
    (isingSpec n B β h) η = fvMeasure η n B β h := rfl

end Ising
end StatMech
