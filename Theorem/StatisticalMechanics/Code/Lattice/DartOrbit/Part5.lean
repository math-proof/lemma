/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartOrbit.lean -/

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
import Def.StatisticalMechanics.Code.Lattice.DartOrbit.Part4
open SimpleGraph Function


namespace StatMech

namespace Lattice

theorem dartOrbitPeriod_pos (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) : 0 < dartOrbitPeriod K a := by
  have hfin : Finite {e : Dart // IsBoundaryDart K e} := (boundaryDarts_finite K hK).to_subtype
  exact Function.minimalPeriod_pos_of_mem_periodicPts
    ((dartNextSub_injective K).mem_periodicPts a)


theorem one_lt_dartOrbitPeriod (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) : 1 < dartOrbitPeriod K a := by
  rcases Nat.lt_or_ge 1 (dartOrbitPeriod K a) with h | h
  · exact h
  · exfalso
    have hpos := dartOrbitPeriod_pos K hK a
    have heq : dartOrbitPeriod K a = 1 := le_antisymm h hpos
    have hfix : Function.IsFixedPt (dartNextSub K) a :=
      Function.minimalPeriod_eq_one_iff_isFixedPt.mp heq
    exact dartNextSub_ne_self K a hfix


theorem dartOrbitPeriod_iterate (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    (dartNextSub K)^[dartOrbitPeriod K a] a = a :=
  Function.iterate_minimalPeriod


end Lattice
end StatMech
