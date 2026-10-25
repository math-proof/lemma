/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_tailinK.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.Umlaufsatz.Part4
open Set SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem kc2_iterate_isBoundaryDart (K : Set (Site 2)) (e : Dart)
    (he : IsBoundaryDart K e) (k : ℕ) :
    IsBoundaryDart K ((dartNext K)^[k] e) := by
  induction k with
  | zero => simpa using he
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact dartNext_isBoundaryDart K _ ih


theorem kc2_iterate_tail_mem (K : Set (Site 2)) (e : Dart)
    (he : IsBoundaryDart K e) (k : ℕ) :
    ((dartNext K)^[k] e).tail ∈ K :=
  (kc2_iterate_isBoundaryDart K e he k).1


theorem kc2_iterate_head_not_mem (K : Set (Site 2)) (e : Dart)
    (he : IsBoundaryDart K e) (k : ℕ) :
    ((dartNext K)^[k] e).head ∉ K :=
  (kc2_iterate_isBoundaryDart K e he k).2


theorem kc2_orbitSub_iterate_tail_mem (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (k : ℕ) :
    ((dartNextSub K)^[k] a).1.tail ∈ K := by
  rw [dartNextSub_iterate_val]
  exact kc2_iterate_tail_mem K a.1 a.2 k


theorem kc2_orbit_support_tail_mem (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) {d : {e : Dart // IsBoundaryDart K e}}
    (_hd : d ∈ (dartOrbitWalk K a).support) :
    d.1.tail ∈ K :=
  d.2.1


end Walls
end StatMech
