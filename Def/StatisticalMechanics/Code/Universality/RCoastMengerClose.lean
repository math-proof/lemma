/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RCoastMengerClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
import Theorem.StatisticalMechanics.Code.Universality.JordanExhaustivityClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.PlanarMengerDualityClose.Part4
import Theorem.StatisticalMechanics.Code.Universality.MengerBarrierClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.CoastlineContinuityClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.CoastlineAnchorClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.CircuitReachClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.BoxArcConnectsClose.Part4
import Theorem.StatisticalMechanics.Code.Universality.RCoastMengerClose
open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

def rcm_RCoastConnectedAll (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) : Prop :=
  ∀ f g : Site 2, bac_IsRCoastFace ω n f → bac_IsRCoastFace ω n g →
    (pmd_boxFaceBarrier ω n).Reachable f g


end Universality
end StatMech
