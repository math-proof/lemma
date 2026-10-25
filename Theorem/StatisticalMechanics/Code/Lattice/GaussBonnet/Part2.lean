/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/GaussBonnet.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.Cyclomatic.Part2
import Def.StatisticalMechanics.Code.Lattice.GaussBonnet.Part2
open SimpleGraph Function


namespace StatMech

namespace Lattice

theorem gaussBonnet_local_global (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    totalTurnZ K a.1 (dartOrbitPeriod K a) = 4 * revCount K a := by
  unfold revCount
  rw [Int.mul_ediv_cancel' (four_dvd_orbit_totalTurnZ K a)]


theorem turningIsFullRevolution_iff_revCount (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    TurningIsFullRevolution K a ↔ (revCount K a = 1 ∨ revCount K a = -1) := by
  unfold TurningIsFullRevolution
  rw [gaussBonnet_local_global K a]
  constructor
  · rintro (h | h)
    · left; omega
    · right; omega
  · rintro (h | h)
    · left; rw [h]; ring
    · right; rw [h]; ring


theorem turningIsFullRevolution_of_revCount (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (h : revCount K a = 1 ∨ revCount K a = -1) :
    TurningIsFullRevolution K a :=
  (turningIsFullRevolution_iff_revCount K a).mpr h


theorem cycleGraph_card_edges (n : ℕ) :
    (cycleGraph (n + 3)).edgeFinset.card = n + 3 := by
  have hsum : ∑ v : Fin (n + 3), (cycleGraph (n + 3)).degree v
      = 2 * (cycleGraph (n + 3)).edgeFinset.card :=
    sum_degrees_eq_twice_card_edges _
  have hsum2 : ∑ v : Fin (n + 3), (cycleGraph (n + 3)).degree v = 2 * (n + 3) := by
    rw [Finset.sum_congr rfl (fun v _ => cycleGraph_degree_three_le)]
    simp [Finset.sum_const, Finset.card_univ]
    ring
  omega


theorem cycleGraph_cyclomaticNumber_eq_one (n : ℕ) :
    cyclomaticNumber (cycleGraph (n + 3)) = 1 := by
  unfold cyclomaticNumber
  rw [cycleGraph_card_edges]
  simp


theorem cycleGraph_not_isAcyclic (n : ℕ) : ¬ (cycleGraph (n + 3)).IsAcyclic := by
  rw [← cyclomaticNumber_eq_zero_iff_isAcyclic cycleGraph_connected]
  rw [cycleGraph_cyclomaticNumber_eq_one]
  decide


theorem orbitEnum_injective (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    Function.Injective
      (fun i : Fin (dartOrbitPeriod K a) => (dartNextSub K)^[i.val] a) := by
  intro i j h
  simp only at h
  have hmp : dartOrbitPeriod K a = Function.minimalPeriod (dartNextSub K) a := rfl
  have := Function.iterate_injOn_Iio_minimalPeriod (f := dartNextSub K) (x := a)
    (Set.mem_Iio.mpr (by rw [← hmp]; exact i.isLt))
    (Set.mem_Iio.mpr (by rw [← hmp]; exact j.isLt)) h
  exact Fin.ext this

open Classical in


theorem contour_card_darts (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    (Finset.univ.image
      (fun i : Fin (dartOrbitPeriod K a) => (dartNextSub K)^[i.val] a)).card
      = dartOrbitPeriod K a := by
  rw [Finset.card_image_of_injective _ (orbitEnum_injective K a), Finset.card_univ,
    Fintype.card_fin]


end Lattice
end StatMech
