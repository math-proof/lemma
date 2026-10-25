/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.jc2_engine
import Theorem.StatisticalMechanics.Code.Walls.jc2_runframe.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc2_thinpendant
import Theorem.StatisticalMechanics.Code.Walls.jc2_thinconn
import Theorem.StatisticalMechanics.Code.Walls.jc2_thinthickdichotomy.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc2_thickshelf.Part3
import Theorem.StatisticalMechanics.Code.Walls.jc_core
import Theorem.StatisticalMechanics.Code.Lattice.BalancePreservingContraction.Part4
import Def.StatisticalMechanics.Code.Walls.jc2_core
open SimpleGraph Function Set


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem jc2_contraction_of_orbitMatch (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (h : jc2_OrbitMatchAt K a) :
    ∃ (K' : Set (Site 2)) (_ : K'.Finite) (_ : K'.Nonempty)
      (a' : {e : Dart // IsBoundaryDart K' e}),
      K'.ncard < K.ncard ∧ cornerBalance K' a' = cornerBalance K a := by
  obtain ⟨K', hK'fin, hK'ne, a', m, m', n, hcard, hp, hp', hmatch, hbal⟩ := h
  refine ⟨K', hK'fin, hK'ne, a', hcard, ?_⟩
  rw [cornerBalance_eq_totalTurnZ, cornerBalance_eq_totalTurnZ, hp, hp']
  exact jc2_engine K K' a.1 a'.1 m m' n hmatch hbal


theorem jc2_orbitMatch_of_contraction (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (h : ∃ (K' : Set (Site 2)) (_ : K'.Finite) (_ : K'.Nonempty)
      (a' : {e : Dart // IsBoundaryDart K' e}),
      K'.ncard < K.ncard ∧ cornerBalance K' a' = cornerBalance K a) :
    jc2_OrbitMatchAt K a := by
  obtain ⟨K', hK'fin, hK'ne, a', hcard, hbalance⟩ := h
  refine ⟨K', hK'fin, hK'ne, a', dartOrbitPeriod K a, dartOrbitPeriod K' a', 0,
    hcard, by omega, by omega, by intro i hi; omega, ?_⟩
  rw [jc_windowTurn_eq, jc_windowTurn_eq, ← umEar_totalTurnZ_eq_window,
      ← umEar_totalTurnZ_eq_window, ← cornerBalance_eq_totalTurnZ, ← cornerBalance_eq_totalTurnZ]
  exact hbalance


theorem jc2_orbitMatch_iff_contraction (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    jc2_OrbitMatchAt K a ↔
      ∃ (K' : Set (Site 2)) (_ : K'.Finite) (_ : K'.Nonempty)
        (a' : {e : Dart // IsBoundaryDart K' e}),
        K'.ncard < K.ncard ∧ cornerBalance K' a' = cornerBalance K a :=
  ⟨jc2_contraction_of_orbitMatch K a, jc2_orbitMatch_of_contraction K a⟩


end Walls
end StatMech
