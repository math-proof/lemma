/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fwrfaceregion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanFaithfulCount.Part6
import Theorem.StatisticalMechanics.Code.Walls.rpccrossflip.Part4
import Theorem.StatisticalMechanics.Code.Walls.ceosimplecycle
import Theorem.StatisticalMechanics.Code.Walls.dowdartwinding
import Theorem.StatisticalMechanics.Code.Walls.kwceventtocut.Part3
import Theorem.StatisticalMechanics.Code.Walls.fwrfaceregion
open Set SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Walls

open StatMech.Lattice


def fwr_faceInside {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) : Site 2 → Prop :=
  fun f => ¬ Even (jec_rayCount (![f 0 + 1, f 1 + 1] : Site 2) Vc)


end Walls
end StatMech
