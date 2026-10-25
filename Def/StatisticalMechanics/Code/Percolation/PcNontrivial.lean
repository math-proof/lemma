/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcNontrivial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.Theta
import Def.StatisticalMechanics.Code.Percolation.TildePc.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.Harris
import Theorem.StatisticalMechanics.Code.Percolation.PcNontrivial
open MeasureTheory Set SimpleGraph
open scoped NNReal ENNReal
open Finset

set_option linter.deprecated false
set_option linter.style.longLine false


namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {d : ℕ}


def vertOf (g : ℕ → Fin d × Bool) : ℕ → Site d
  | 0 => origin d
  | (k + 1) => coordShift (vertOf g k) (g k).1 (stepSign (g k).2)

end Percolation
end StatMech
