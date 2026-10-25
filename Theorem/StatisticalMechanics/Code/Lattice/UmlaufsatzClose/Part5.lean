/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.TurningNumber.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CornerBalance.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EarRemoval.Part5
import Theorem.StatisticalMechanics.Code.Lattice.EarExistence.Part4
import Theorem.StatisticalMechanics.Code.Lattice.GaussBonnet.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Theorem.StatisticalMechanics.Code.Lattice.UmlaufsatzBaseCases.Part3
import Theorem.StatisticalMechanics.Code.Lattice.UmlaufsatzEar.Part2
import Theorem.StatisticalMechanics.Code.Lattice.GaussBonnetEar
import Theorem.StatisticalMechanics.Code.Lattice.BalancePreservingContraction.Part4
import Def.StatisticalMechanics.Code.Lattice.UmlaufsatzClose.Part5
open SimpleGraph Function Set


namespace StatMech

namespace Lattice

theorem uc_generalFullRevolution_of_saturating (hsat : bpc_BalanceSaturatingContraction) :
    uc_GeneralFullRevolution :=
  fun K hK hne a => uc_turningIsFullRevolution hsat K hK hne a


theorem uc_generalEulerCharOne_of_saturating (hsat : bpc_BalanceSaturatingContraction) :
    uc_GeneralEulerCharOne := by
  intro K hK hne a
  have hrev : TurningIsFullRevolution K a := uc_turningIsFullRevolution hsat K hK hne a
  have hp : 3 ≤ dartOrbitPeriod K a := by
    have := orbitPeriod_ge_four_of_fullRevolution K a hrev; omega
  exact (eulerCharOne_iff_turningIsFullRevolution K a hp).mpr hrev


theorem uc_fullRevolution_of_eulerCharOne_period (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (hp : 3 ≤ dartOrbitPeriod K a)
    (h : EulerCharOne K a) : TurningIsFullRevolution K a :=
  turningIsFullRevolution_of_eulerCharOne K a hp h


theorem uc_verticalDomino_eulerCharOne :
    EulerCharOne (uc_rotSet domino) (uc_rotSub domino dmBase) := by
  have hrev : TurningIsFullRevolution (uc_rotSet domino) (uc_rotSub domino dmBase) :=
    uc_verticalDomino_totalTurn_eq_four
  have hp : 3 ≤ dartOrbitPeriod (uc_rotSet domino) (uc_rotSub domino dmBase) := by
    have := orbitPeriod_ge_four_of_fullRevolution (uc_rotSet domino) (uc_rotSub domino dmBase) hrev
    omega
  exact (eulerCharOne_iff_turningIsFullRevolution (uc_rotSet domino) (uc_rotSub domino dmBase) hp).mpr
    hrev


end Lattice
end StatMech
