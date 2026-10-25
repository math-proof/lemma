/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean -/

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
import Def.StatisticalMechanics.Code.Lattice.EarContraction.Part8
open SimpleGraph Function


namespace StatMech

namespace Lattice

theorem balanceIsFour_iff_simplePolygon (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    BalanceIsFour K a ↔ SimplePolygonCornerBalance K a :=
  (simplePolygonCornerBalance_iff_cornerBalance K a).symm


theorem singleton_balanceIsFour (v : Site 2)
    (a : {e : Dart // IsBoundaryDart ({v} : Set (Site 2)) e}) :
    BalanceIsFour ({v} : Set (Site 2)) a :=
  Or.inr (singleton_cornerBalance v a)


end Lattice
end StatMech
