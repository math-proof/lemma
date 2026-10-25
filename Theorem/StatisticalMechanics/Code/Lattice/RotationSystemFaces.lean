/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RotationSystemFaces.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.InsideConnected.Part2
import Theorem.StatisticalMechanics.Code.Lattice.FaceComponentBijection.Part2
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

theorem rsf_boundaryDart_tail_mem (C : Set (Site 2)) {e : Dart} (he : IsBoundaryDart C e) :
    e.tail ∈ C := he.1


theorem rsf_boundaryDart_head_not_mem (C : Set (Site 2)) {e : Dart} (he : IsBoundaryDart C e) :
    e.head ∉ C := he.2


theorem rsf_no_shared_boundaryDart {C C' : Set (Site 2)} (hCC' : Disjoint C C')
    {e : Dart} (he : IsBoundaryDart C e) (he' : IsBoundaryDart C' e) : False := by
  exact (Set.disjoint_left.mp hCC') he.1 he'.1


theorem rsf_disjoint_boundaryDarts_of_disjoint {C C' : Set (Site 2)} (hCC' : Disjoint C C') :
    Disjoint {e : Dart | IsBoundaryDart C e} {e : Dart | IsBoundaryDart C' e} := by
  rw [Set.disjoint_left]
  intro e he he'
  exact rsf_no_shared_boundaryDart hCC' he he'


theorem rsf_orbit_isBoundaryDart (C : Set (Site 2)) {e : Dart} (he : IsBoundaryDart C e)
    (k : ℕ) : IsBoundaryDart C ((dartNext C)^[k] e) := by
  induction k with
  | zero => exact he
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact dartNext_isBoundaryDart C ((dartNext C)^[n] e) ih


theorem rsf_orbit_tail_mem (C : Set (Site 2)) {e : Dart} (he : IsBoundaryDart C e) (k : ℕ) :
    ((dartNext C)^[k] e).tail ∈ C :=
  (rsf_orbit_isBoundaryDart C he k).1


theorem rsf_orbit_head_not_mem (C : Set (Site 2)) {e : Dart} (he : IsBoundaryDart C e) (k : ℕ) :
    ((dartNext C)^[k] e).head ∉ C :=
  (rsf_orbit_isBoundaryDart C he k).2


end Lattice
end StatMech
