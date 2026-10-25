/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusLaplacianNormalization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusGraph.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusExponentialMoment
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Def.StatisticalMechanics.Code.FrontierA.IsingTorusLaplacianNormalization
open Finset Matrix
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}


theorem isingTorusOrientedIndexedDart_bijective :
    Function.Bijective
      (isingTorusOrientedIndexedDart (d := d) (k := k)) := by
  constructor
  · rintro ⟨p, b⟩ ⟨q, c⟩ h
    have hedge_oriented
        (r : (IsingDyadicTorus d k × Fin d) × Bool) :
        (isingTorusOrientedIndexedDart r).edge =
          isingTorusIndexedEdge r.1 := by
      unfold isingTorusOrientedIndexedDart
      split <;>
        simp [isingTorusIndexedDart, isingTorusIndexedEdge]
    have hedge : isingTorusIndexedEdge p = isingTorusIndexedEdge q := by
      rw [← hedge_oriented (p, b), h, hedge_oriented]
    have hpq := isingTorusIndexedEdge_injective
      (d := d) (k := k) hedge
    subst q
    cases b <;> cases c
    · rfl
    · have hne := (isingTorusIndexedDart p).symm_ne
      exact (hne h.symm).elim
    · have hne := (isingTorusIndexedDart p).symm_ne
      exact (hne h).elim
    · rfl
  · intro dart
    have hedgeMem : dart.edge ∈ (isingTorusGraph d k).edgeFinset := by
      rw [SimpleGraph.mem_edgeFinset]
      exact dart.edge_mem
    obtain ⟨p, hp⟩ := isingTorusIndexedEdge_surjective
      (d := d) (k := k) ⟨dart.edge, hedgeMem⟩
    have hedge : dart.edge = (isingTorusIndexedDart p).edge := by
      have hp' := congrArg Subtype.val hp
      simpa [isingTorusIndexedDart, isingTorusIndexedEdge] using hp'.symm
    rcases (SimpleGraph.dart_edge_eq_iff dart
      (isingTorusIndexedDart p)).mp hedge with h | h
    · exact ⟨(p, false), by
        simpa [isingTorusOrientedIndexedDart] using h.symm⟩
    · exact ⟨(p, true), by
        simpa [isingTorusOrientedIndexedDart] using h.symm⟩


end StatMech.FrontierA
