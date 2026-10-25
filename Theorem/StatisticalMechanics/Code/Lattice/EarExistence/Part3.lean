/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarExistence.lean -/

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
import Structure.StatisticalMechanics.Code.Lattice.EarExistence
open SimpleGraph Function


namespace StatMech

namespace Lattice

theorem exists_extremeCell (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty) :
    ∃ c, IsExtremeCell K c := by
  have hfne : hK.toFinset.Nonempty := by rwa [Set.Finite.toFinset_nonempty]
  obtain ⟨c, hc, hmax⟩ := Finset.exists_max_image hK.toFinset lexKey hfne
  refine ⟨c, ⟨by rwa [Set.Finite.mem_toFinset] at hc, ?_⟩⟩
  intro v hv
  exact hmax v (by rwa [Set.Finite.mem_toFinset])


theorem extremeCell_not_mem_of_higher (K : Set (Site 2)) (c v : Site 2)
    (hc : IsExtremeCell K c) (hy : c 1 < v 1) : v ∉ K := by
  intro hv
  have h := hc.maximal v hv
  unfold lexKey at h
  rw [Prod.Lex.toLex_le_toLex] at h
  rcases h with h | ⟨h1, h2⟩ <;> omega


theorem extremeCell_not_mem_of_left (K : Set (Site 2)) (c v : Site 2)
    (hc : IsExtremeCell K c) (hy : v 1 = c 1) (hx : v 0 < c 0) : v ∉ K := by
  intro hv
  have h := hc.maximal v hv
  unfold lexKey at h
  rw [Prod.Lex.toLex_le_toLex] at h
  rcases h with h | ⟨h1, h2⟩ <;> omega


theorem extremeCell_front_nmem (K : Set (Site 2)) (c : Site 2) (hc : IsExtremeCell K c) :
    (leftDart c).head + (-rot90Fun (leftDart c).dir) ∉ K := by
  apply extremeCell_not_mem_of_higher K c _ hc
  rw [leftDart_front_coord1]; omega


theorem extremeCell_side_nmem (K : Set (Site 2)) (c : Site 2) (hc : IsExtremeCell K c) :
    (leftDart c).tail + (-rot90Fun (leftDart c).dir) ∉ K := by
  apply extremeCell_not_mem_of_higher K c _ hc
  rw [leftDart_side_coord1]; omega


theorem extremeCell_head_nmem (K : Set (Site 2)) (c : Site 2) (hc : IsExtremeCell K c) :
    (leftDart c).head ∉ K := by
  apply extremeCell_not_mem_of_left K c _ hc
  · rw [leftDart_head_coord1]
  · rw [leftDart_head_coord0]; omega


theorem extremeCell_boundary (K : Set (Site 2)) (c : Site 2) (hc : IsExtremeCell K c) :
    IsBoundaryDart K (leftDart c) :=
  ⟨by rw [leftDart_tail]; exact hc.mem, extremeCell_head_nmem K c hc⟩


theorem extremeCell_turnZ (K : Set (Site 2)) (c : Site 2) (hc : IsExtremeCell K c) :
    turnZ K (leftDart c) = -1 := by
  unfold turnZ
  rw [if_neg (extremeCell_front_nmem K c hc), if_neg (extremeCell_side_nmem K c hc)]


theorem exists_convex_corner_dart (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty) :
    ∃ e : Dart, IsBoundaryDart K e ∧ turnZ K e = -1 := by
  obtain ⟨c, hc⟩ := exists_extremeCell K hK hne
  exact ⟨leftDart c, extremeCell_boundary K c hc, extremeCell_turnZ K c hc⟩


theorem one_le_leftCornerCount_of_first (K : Set (Site 2)) (e : Dart) (p : ℕ) (hp : 0 < p)
    (h0 : turnZ K e = -1) : 1 ≤ leftCornerCount K e p := by
  classical
  unfold leftCornerCount
  have hmem : 0 ∈ (Finset.range p).filter (fun i => turnZ K ((dartNext K)^[i] e) = -1) := by
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨hp, by rw [Function.iterate_zero_apply]; exact h0⟩
  have : 1 ≤ ((Finset.range p).filter
      (fun i => turnZ K ((dartNext K)^[i] e) = -1)).card :=
    Finset.card_pos.mpr ⟨0, hmem⟩
  exact_mod_cast this


end Lattice
end StatMech
