/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TreeNonBridgeProve.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces.Part3
import Theorem.StatisticalMechanics.Code.Lattice.FloodFillConnected.Part3
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ArcNoSeparation.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ArcExteriorClose.Part3
import Theorem.StatisticalMechanics.Code.Lattice.TreeNonBridgeProve.Part3
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

variable {V : Type*}


def tnbp_RingChain : List (Site 2) → Prop
  | [] => True
  | c :: L' => tnbp_RingConnected c {x : Site 2 | x ∈ L'} ∧ tnbp_RingChain L'

end Lattice
end StatMech
