/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABFiniteSymmetry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.ABFiniteAssembly.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
open Finset Set SimpleGraph


namespace StatMech

namespace Sharpness

open ConfigSpace RandomCurrent

variable {E F : Type*} [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]

noncomputable def abfsLaw (p : E -> Real) (e : E) (b : Bool) : Real :=
  if b then p e else 1 - p e

end Sharpness
end StatMech
