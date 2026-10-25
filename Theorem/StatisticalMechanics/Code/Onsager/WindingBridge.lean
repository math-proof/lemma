/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WindingBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.InteriorReaches
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Def.StatisticalMechanics.Code.Onsager.WindingBridge


namespace StatMech.Onsager.WindingBridge

open StatMech.Lattice

open StatMech.Onsager.ChordCut

open StatMech.Onsager.InteriorReaches


@[simp] theorem toSite_zero (p : Pt) : toSite p 0 = p.1 := by simp [toSite]

@[simp] theorem toSite_one (p : Pt) : toSite p 1 = p.2 := by simp [toSite]


theorem toSite_injective : Function.Injective toSite := by
  intro a b h
  have h0 : toSite a 0 = toSite b 0 := by rw [h]
  have h1 : toSite a 1 = toSite b 1 := by rw [h]
  simp only [toSite_zero, toSite_one] at h0 h1
  exact Prod.ext h0 h1


theorem shift_injective : Function.Injective (fun p : Pt => (p.1 + 1, p.2)) := by
  intro a b h
  simp only [Prod.mk.injEq] at h
  exact Prod.ext (by omega) h.2


theorem toSite_adj_shift (p : Pt) :
    (hypercubicLattice 2).Adj (toSite p) (toSite (p.1 + 1, p.2)) := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]
  simp only [toSite_zero, toSite_one]
  omega


theorem barrier_of_side_change (S : Set (Site 2)) {x y : Site 2}
    (hadj : (hypercubicLattice 2).Adj x y) (hchg : ¬ (x ∈ S ↔ y ∈ S)) :
    bdEdge S s(x, y) := by
  by_contra hnb
  have hadj' : (latticeMinusBarrier S).Adj x y := ⟨hadj, hnb⟩
  exact hchg (latticeMinusBarrier_sameSide S hadj'.toWalk)


end StatMech.Onsager.WindingBridge
