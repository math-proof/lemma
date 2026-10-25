/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TurningNumber.lean -/

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
import Def.StatisticalMechanics.Code.Lattice.TurningNumber.Part4
open SimpleGraph Function


namespace StatMech

namespace Lattice

@[simp] theorem totalTurnZ_zero (K : Set (Site 2)) (e : Dart) : totalTurnZ K e 0 = 0 := by
  simp [totalTurnZ]


theorem totalTurnZ_cast_eq_cumTurn (K : Set (Site 2)) (e : Dart) (p : ℕ) :
    ((totalTurnZ K e p : ℤ) : ZMod 4) = cumTurn K e p := by
  unfold totalTurnZ cumTurn
  push_cast
  exact Finset.sum_congr rfl (fun i _ => turnZ_cast_eq_turn K _)


theorem abs_totalTurnZ_le (K : Set (Site 2)) (e : Dart) (p : ℕ) :
    |totalTurnZ K e p| ≤ (p : ℤ) := by
  unfold totalTurnZ
  calc |∑ i ∈ Finset.range p, turnZ K ((dartNext K)^[i] e)|
      ≤ ∑ i ∈ Finset.range p, |turnZ K ((dartNext K)^[i] e)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range p, (1 : ℤ) :=
        Finset.sum_le_sum (fun i _ => abs_turnZ_le_one K _)
    _ = (p : ℤ) := by simp


theorem cumTurn_eq_zero_of_iterate_eq (K : Set (Site 2)) (e : Dart) (p : ℕ)
    (hp : (dartNext K)^[p] e = e) : cumTurn K e p = 0 := by
  have hdir : ((dartNext K)^[p] e).dir = e.dir := by rw [hp]
  rw [dir_iterate_eq_rotPow_cumTurn] at hdir
  exact (rotPow_dir_eq_iff e (cumTurn K e p)).mp hdir


theorem four_dvd_totalTurnZ_of_iterate_eq (K : Set (Site 2)) (e : Dart) (p : ℕ)
    (hp : (dartNext K)^[p] e = e) : (4 : ℤ) ∣ totalTurnZ K e p := by
  have hz : ((totalTurnZ K e p : ℤ) : ZMod 4) = 0 := by
    rw [totalTurnZ_cast_eq_cumTurn]; exact cumTurn_eq_zero_of_iterate_eq K e p hp
  have hdvd : ((4 : ℕ) : ℤ) ∣ totalTurnZ K e p :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp hz
  exact_mod_cast hdvd


theorem orbit_iterate_period_eq (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    (dartNext K)^[dartOrbitPeriod K a] a.1 = a.1 := by
  have h := dartOrbitPeriod_iterate K a
  have h2 := congrArg Subtype.val h
  rwa [dartNextSub_iterate_val] at h2


theorem dartOrbitPeriod_cumTurn_eq_zero (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    cumTurn K a.1 (dartOrbitPeriod K a) = 0 :=
  cumTurn_eq_zero_of_iterate_eq K a.1 (dartOrbitPeriod K a) (orbit_iterate_period_eq K a)


theorem four_dvd_orbit_totalTurnZ (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    (4 : ℤ) ∣ totalTurnZ K a.1 (dartOrbitPeriod K a) :=
  four_dvd_totalTurnZ_of_iterate_eq K a.1 (dartOrbitPeriod K a) (orbit_iterate_period_eq K a)


theorem abs_orbit_totalTurnZ_le (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    |totalTurnZ K a.1 (dartOrbitPeriod K a)| ≤ (dartOrbitPeriod K a : ℤ) :=
  abs_totalTurnZ_le K a.1 (dartOrbitPeriod K a)


end Lattice
end StatMech
