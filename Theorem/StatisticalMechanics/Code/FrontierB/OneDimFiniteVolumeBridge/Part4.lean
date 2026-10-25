/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.OneDimTransferPerron
import Theorem.StatisticalMechanics.Code.Ising.FVConsistencyProve.Part2
import Theorem.StatisticalMechanics.Code.Lattice.ContourCountInjection.Part2
import Def.StatisticalMechanics.Code.FrontierB.OneDimFiniteVolumeBridge.Part4
open scoped BigOperators
open Finset Matrix


namespace StatMech.FrontierB

open StatMech.Lattice StatMech.Ising StatMech.FrontierC


lemma adjacent_site1_eq_chainBond (x y : Site 1)
    (hadj : (hypercubicLattice 1).Adj x y) :
    ∃ z : ℤ, s(x, y) = chainBond z := by
  rw [hypercubicLattice_adj, Fin.sum_univ_one] at hadj
  change (site1Coord x - site1Coord y).natAbs = 1 at hadj
  have hcoord := Int.natAbs_eq (site1Coord x - site1Coord y)
  rw [hadj] at hcoord
  rcases hcoord with h | h
  · refine ⟨site1Coord y, ?_⟩
    rw [← site1_site1Coord x, ← site1_site1Coord y]
    unfold chainBond
    rw [show site1Coord x = site1Coord y + 1 by omega]
    exact Sym2.eq_swap
  · refine ⟨site1Coord x, ?_⟩
    rw [← site1_site1Coord x, ← site1_site1Coord y]
    unfold chainBond
    rw [show site1Coord y = site1Coord x + 1 by omega]
    simp


theorem chainBondFinset_eq_bondFinsetTouch (n : ℕ) :
    chainBondFinset n = bondFinsetTouch 1 n := by
  ext e
  constructor
  · intro he
    rw [chainBondFinset, Finset.mem_image] at he
    obtain ⟨z, hz, rfl⟩ := he
    rw [Finset.mem_Icc] at hz
    exact (chainBond_mem_bondFinsetTouch_iff z n).mpr hz
  · intro he
    induction e with
    | h x y =>
      have hdata := (mem_bondFinsetTouch_mk_iff n x y).mp he
      obtain ⟨z, hz⟩ := adjacent_site1_eq_chainBond x y hdata.1
      rw [chainBondFinset, Finset.mem_image]
      refine ⟨z, ?_, hz.symm⟩
      rw [Finset.mem_Icc, ← chainBond_mem_bondFinsetTouch_iff z n, ← hz]
      exact he


lemma site1_injective : Function.Injective site1 := intEquivSite1.injective

lemma chainBond_injective : Function.Injective chainBond := by
  intro z w h
  unfold chainBond at h
  rw [Sym2.eq_iff] at h
  rcases h with ⟨h1, _⟩ | ⟨h1, h2⟩
  · exact site1_injective h1
  · have hz : z = w + 1 := site1_injective h1
    have hw : z + 1 = w := site1_injective h2
    omega


end StatMech.FrontierB
