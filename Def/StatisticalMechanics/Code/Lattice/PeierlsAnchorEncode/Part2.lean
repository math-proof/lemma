/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsAnchorEncode.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.ContourSubsetCount
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsAnchorEncode
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

attribute [local instance] Classical.propDecidable

variable {d : ℕ}


def axisVertex (d j : ℕ) : Site d := fun i => if i.val = 0 then (j : ℤ) else 0

end Lattice
end StatMech
