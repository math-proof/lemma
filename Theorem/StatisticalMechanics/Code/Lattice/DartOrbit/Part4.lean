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
import Def.StatisticalMechanics.Code.Lattice.DartOrbit.Part3
open SimpleGraph Function


namespace StatMech

namespace Lattice

theorem orbitWalkAux_length (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (n : ℕ) : (orbitWalkAux K a n).length = n := by
  induction n with
  | zero => rfl
  | succ m ih => simp only [orbitWalkAux, SimpleGraph.Walk.length_concat, ih]


theorem orbitWalkAux_support (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (n : ℕ) :
    (orbitWalkAux K a n).support = (List.range (n + 1)).map (fun k => (dartNextSub K)^[k] a) := by
  induction n with
  | zero => simp [orbitWalkAux]
  | succ m ih =>
    show ((orbitWalkAux K a m).concat _).support = _
    rw [SimpleGraph.Walk.support_concat, ih, List.range_succ (n := m + 1), List.map_append]
    simp


end Lattice
end StatMech
