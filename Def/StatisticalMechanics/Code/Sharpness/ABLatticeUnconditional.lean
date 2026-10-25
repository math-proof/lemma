/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABLatticeUnconditional.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.ABInfiniteGhost.Part13
import Theorem.StatisticalMechanics.Code.FK.TranslationCofinal.Part2
open Filter MeasureTheory Set SimpleGraph Topology
open scoped BigOperators


namespace StatMech

namespace Sharpness

open ConfigSpace

open StatMech.Lattice


noncomputable def ablBoxFinset (d n : Nat) : Finset (Site d) :=
  (box_finite d n).toFinset

end Sharpness
end StatMech
