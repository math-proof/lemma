/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyCorrect.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanBridgeCycle.Part10
import Def.StatisticalMechanics.Code.Lattice.WhitneyCorrect.Part6
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem whc_faithful_square_nonempty :
    Nonempty {c : (whb_faceRegion (imageGraph jbc_Pce)).ConnectedComponent // c.supp.Finite} :=
  ⟨⟨(whb_faceRegion (imageGraph jbc_Pce)).connectedComponentMk ![0, 0],
    whb_faceRegion_interior_bounded⟩⟩

end Lattice
end StatMech
