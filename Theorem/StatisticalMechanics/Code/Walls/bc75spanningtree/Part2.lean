/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc75spanningtree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc74disjointforest.Part2
import Theorem.StatisticalMechanics.Code.Percolation.OpenSpanningForestClose.Part4
import Theorem.StatisticalMechanics.Code.Percolation.SingleLeafHallClose.Part2
import Def.StatisticalMechanics.Code.Walls.bc75spanningtree.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc75_arm_adjacent_hub {ω : ConfigSpace (Sym2 (Site d))} {L R : ℕ}
    {c : Fin d → Fin (2 * L + 1)} {y a : Site d}
    (hy : y ∈ bc73_fiber ω L R c) (hinc : bc67_GnIncident ω L y a)
    (hane : bc75_collapseFiber ω L R c a = a) (hay : a ≠ y) :
    (bc75_fiberQuot ω L R c).Adj y a := by
  obtain ⟨b, hbbox, hadj⟩ := hinc
  refine ⟨hay.symm, b, a, ?_, hane, hadj⟩
  exact bc75_collapseFiber_eq hy hbbox


theorem bc75_fiberQuot_adj_iff {ω : ConfigSpace (Sym2 (Site d))} {L R : ℕ}
    {c : Fin d → Fin (2 * L + 1)} {u v : Site d} :
    (bc75_fiberQuot ω L R c).Adj u v ↔
      u ≠ v ∧ ∃ p q, bc75_collapseFiber ω L R c p = u ∧
        bc75_collapseFiber ω L R c q = v ∧ (openSubgraph d ω).Adj p q :=
  Iff.rfl


theorem bc75_gnCut_of_doubleInduce {ω : ConfigSpace (Sym2 (Site d))} {L R : ℕ}
    {c : Fin d → Fin (2 * L + 1)} {y : Site d} {S : Set (Site d)} (hyS : y ∈ S)
    {a₁ a₂ : (↑S : Type)} (h1 : a₁ ≠ ⟨y, hyS⟩) (h2 : a₂ ≠ ⟨y, hyS⟩)
    (h : (((bc75_fiberQuot ω L R c).induce S).induce
        ({(⟨y, hyS⟩ : (↑S : Type))}ᶜ : Set (↑S : Type))).Reachable
      ⟨a₁, by simpa using h1⟩ ⟨a₂, by simpa using h2⟩) :
    ((bc75_fiberQuot ω L R c).induce ({y}ᶜ : Set (Site d))).Reachable
      ⟨(a₁ : Site d), by simpa using fun hh => h1 (Subtype.ext hh)⟩
      ⟨(a₂ : Site d), by simpa using fun hh => h2 (Subtype.ext hh)⟩ := by
  obtain ⟨w⟩ := h
  set Q := bc75_fiberQuot ω L R c with hQ
  
  set g : (((Q.induce S).induce ({(⟨y, hyS⟩ : (↑S : Type))}ᶜ : Set (↑S : Type)))) →g
        (Q.induce ({y}ᶜ : Set (Site d))) :=
    { toFun := fun u => ⟨(u.1.1 : Site d), by
        have : u.1 ≠ (⟨y, hyS⟩ : (↑S : Type)) := u.2
        simpa using fun hh => this (Subtype.ext hh)⟩
      map_rel' := fun {u v} huv => huv } with hg
  exact ⟨w.map g⟩


end StatMech.Walls
