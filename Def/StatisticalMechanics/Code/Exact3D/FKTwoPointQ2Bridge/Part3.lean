/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.IsingBridgeTargets.Part17
import Theorem.StatisticalMechanics.Code.FK.TwoPointInfinite.Part5
import Theorem.StatisticalMechanics.Code.FK.BoxTailLimit
import Theorem.StatisticalMechanics.Code.FK.FreeWeakLimit.Part8
import Theorem.StatisticalMechanics.Code.FK.MonotoneWeakLimit.Part2
import Theorem.StatisticalMechanics.Code.FK.FreeWiredAgreeClose.Part3
import Theorem.StatisticalMechanics.Code.Ising.TransitionFK
import Theorem.StatisticalMechanics.Code.Exact3D.FKTwoPointQ2Bridge.Part2
open Filter
open MeasureTheory


namespace StatMech

namespace Exact3D

open FK


noncomputable def freeFiniteVolumeXAxisDetourOfBetaQ2InVolume
    (β : ℝ) (hβ : 0 < β) (N n : ℕ) : ℝ :=
  if hn : n ≤ N then
    ((freeFiniteMeasure 3 N (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β)
        (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
      (boxConnectionDetourEvent 3 hn
        (ising3DOriginBoxVertex n) (ising3DXAxisBoxVertex n)))
  else
    0


noncomputable def freeFiniteVolumeOriginBoundaryConnectionOfBetaQ2InVolume
    (β : ℝ) (hβ : 0 < β) (N n : ℕ) : ℝ :=
  ((freeFiniteMeasure 3 N (Ising.pOfBeta_pos hβ) (Ising.pOfBeta_lt_one β)
      (by norm_num : (0 : ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
    (boxBdryConnEvent 3 n))


end Exact3D
end StatMech
