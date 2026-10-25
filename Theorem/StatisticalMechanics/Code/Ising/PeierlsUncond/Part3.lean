/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsUncond.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.PeierlsFull.Part3
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.FaceRegion.Part3
import Def.StatisticalMechanics.Code.Ising.PeierlsUncond.Part3
open MeasureTheory Filter Topology Finset SimpleGraph
open scoped BigOperators ENNReal


namespace StatMech

namespace Ising

open StatMech.Lattice

attribute [local instance] Classical.propDecidable

variable {d : ℕ}


@[simp] lemma crossEdgeBond_mk (K : Set (Site d)) (σ : ConfigSpace (Site d)) (x y : Site d) :
    crossEdgeBond K σ s(x, y) = if (x ∈ K ↔ y ∉ K) then bond σ s(x, y) else 0 := rfl

lemma crossEdgeBond_of_not_crosses (K : Set (Site d)) (σ : ConfigSpace (Site d))
    {e : Sym2 (Site d)} (he : ¬ crosses K e) : crossEdgeBond K σ e = 0 := by
  induction e with | h x y => rw [crossEdgeBond_mk, if_neg]; rwa [crosses_mk] at he

lemma crossEdgeBond_of_crosses (K : Set (Site d)) (σ : ConfigSpace (Site d))
    {e : Sym2 (Site d)} (he : crosses K e) : crossEdgeBond K σ e = bond σ e := by
  induction e with | h x y => rw [crossEdgeBond_mk, if_pos]; rwa [crosses_mk] at he


lemma bond_flipOnSet_diff (K : Set (Site d)) (σ : ConfigSpace (Site d)) (x y : Site d) :
    bond (flipOnSet K σ) s(x, y) - bond σ s(x, y) = -2 * crossEdgeBond K σ s(x, y) := by
  rw [bond_mk, bond_mk]; unfold crossEdgeBond; simp only [Sym2.lift_mk]
  by_cases hx : x ∈ K <;> by_cases hy : y ∈ K
  · rw [spin_flipOnSet_mem K σ hx, spin_flipOnSet_mem K σ hy, if_neg (by tauto)]; ring
  · rw [spin_flipOnSet_mem K σ hx, spin_flipOnSet_not_mem K σ hy, if_pos (by tauto), bond_mk]
    ring
  · rw [spin_flipOnSet_not_mem K σ hx, spin_flipOnSet_mem K σ hy, if_pos (by tauto), bond_mk]
    ring
  · rw [spin_flipOnSet_not_mem K σ hx, spin_flipOnSet_not_mem K σ hy, if_neg (by tauto)]; ring


lemma bond_flipOnSet_diff_edge (K : Set (Site d)) (σ : ConfigSpace (Site d)) (e : Sym2 (Site d)) :
    bond (flipOnSet K σ) e - bond σ e = -2 * crossEdgeBond K σ e := by
  induction e with | h x y => exact bond_flipOnSet_diff K σ x y


lemma bondSum_flipOnSet_diff (K : Set (Site d)) (σ : ConfigSpace (Site d))
    (B : Finset (Sym2 (Site d))) :
    (∑ e ∈ B, bond (flipOnSet K σ) e) - (∑ e ∈ B, bond σ e)
      = -2 * ∑ e ∈ B, crossEdgeBond K σ e := by
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun e _ => bond_flipOnSet_diff_edge K σ e)


lemma sum_crossEdgeBond (K : Set (Site d)) (σ : ConfigSpace (Site d))
    (B : Finset (Sym2 (Site d))) :
    (∑ e ∈ B, crossEdgeBond K σ e) = ∑ e ∈ crossEdges K B, bond σ e := by
  unfold crossEdges
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  by_cases he : crosses K e
  · rw [if_pos he, crossEdgeBond_of_crosses K σ he]
  · rw [if_neg he, crossEdgeBond_of_not_crosses K σ he]


end Ising
end StatMech
