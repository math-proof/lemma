/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzSingleCycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.TurningNumber.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CornerBalance.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EarRemoval.Part5
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.OrbitEncloses.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanSingleCycle.Part4
import Theorem.StatisticalMechanics.Code.Lattice.Umlaufsatz.Part4
import Def.StatisticalMechanics.Code.Lattice.UmlaufsatzSingleCycle.Part2
open SimpleGraph Function Set Finset


namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}


theorem usc_dir_injOn_visitSet (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (f : Site 2) :
    Set.InjOn (fun i => ((dartNext K)^[i] a.1).dir) (usc_visitSet K a f) := by
  classical
  intro i hi j hj hdir
  simp only [usc_visitSet, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hi hj
  simp only at hdir
  have hface : dartFace ((dartNext K)^[i] a.1) = dartFace ((dartNext K)^[j] a.1) := by
    rw [hi.2, hj.2]
  have hdart : (dartNext K)^[i] a.1 = (dartNext K)^[j] a.1 :=
    dartFace_eq_of_dir_eq hdir hface
  exact orbitDart_injOn K a (Set.mem_Iio.mpr hi.1) (Set.mem_Iio.mpr hj.1) hdart


theorem usc_orbitFace_multiplicity_le_four (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (f : Site 2) :
    (usc_visitSet K a f).card ≤ 4 := by
  classical
  calc (usc_visitSet K a f).card
      ≤ ((usc_visitSet K a f).image (fun i => ((dartNext K)^[i] a.1).dir)).card := by
        rw [Finset.card_image_of_injOn (usc_dir_injOn_visitSet K a f)]
    _ ≤ usc_fourDirs.card := by
        apply Finset.card_le_card
        intro d hd
        rw [Finset.mem_image] at hd
        obtain ⟨i, _, rfl⟩ := hd
        exact usc_dir_mem_fourDirs _
    _ = 4 := usc_fourDirs_card


theorem usc_faceInjOn_iff_visit_le_one (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1)) (Set.Iio (dartOrbitPeriod K a)) ↔
      ∀ f : Site 2, (usc_visitSet K a f).card ≤ 1 := by
  classical
  constructor
  · 
    intro hinj f
    rw [Finset.card_le_one]
    intro i hi j hj
    simp only [usc_visitSet, Finset.mem_filter, Finset.mem_range] at hi hj
    exact hinj (Set.mem_Iio.mpr hi.1) (Set.mem_Iio.mpr hj.1) (by simp only; rw [hi.2, hj.2])
  · 
    intro hcard i hi j hj hface
    simp only [Set.mem_Iio] at hi hj
    simp only at hface
    
    set f := dartFace ((dartNext K)^[i] a.1) with hf
    have hi' : i ∈ usc_visitSet K a f := by
      simp only [usc_visitSet, Finset.mem_filter, Finset.mem_range]; exact ⟨hi, rfl⟩
    have hj' : j ∈ usc_visitSet K a f := by
      simp only [usc_visitSet, Finset.mem_filter, Finset.mem_range]; exact ⟨hj, hface.symm⟩
    exact Finset.card_le_one.mp (hcard f) i hi' j hj'


theorem usc_noPinch_iff_singleVisit (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    OrbitFaceNoPinch K a ↔ ∀ f : Site 2, (usc_visitSet K a f).card ≤ 1 := by
  rw [← orbitFace_injOn_iff_dir_collision K a]
  exact usc_faceInjOn_iff_visit_le_one K a


end Lattice
end StatMech
