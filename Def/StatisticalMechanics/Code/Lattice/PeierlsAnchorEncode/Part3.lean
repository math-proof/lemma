/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsAnchorEncode.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.ContourSubsetCount
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsAnchorEncode.Part2
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

attribute [local instance] Classical.propDecidable

variable {d : ℕ}


noncomputable def axisAnchorPool (d ℓ : ℕ) : Finset (Site d) :=
  (Finset.range ℓ).image (fun j => axisVertex d j)


end Lattice
end StatMech
