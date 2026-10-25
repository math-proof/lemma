/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusSquareCrossingCover.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusSquareCrossingCounterexample
import Theorem.StatisticalMechanics.Code.Universality.ConnectedRCoastClose.Part13
import Theorem.StatisticalMechanics.Code.Universality.BXPAllAspect
import Def.StatisticalMechanics.Code.BeffaraDC.TorusSquareCrossingCover.Part2
open SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Lattice

open StatMech.Onsager

open StatMech.RSW.Box

open StatMech.Universality


theorem torusReduceSite_adj (L : ℕ) [Fact (2 < L)] {x y : Site 2}
    (hxy : (hypercubicLattice 2).Adj x y) :
    (onsTorusGraph L).Adj (torusReduceSite L x) (torusReduceSite L y) := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hxy
  change onsTorusAdj L _ _
  unfold onsTorusAdj torusReduceSite
  have key :
      ((x 0 - y 0).natAbs = 1 ∧ (x 1 - y 1).natAbs = 0) ∨
      ((x 0 - y 0).natAbs = 0 ∧ (x 1 - y 1).natAbs = 1) := by
    omega
  rcases key with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · have hy : x 1 = y 1 := by omega
    right
    refine ⟨by simpa using congrArg (fun z : ℤ => (z : ZMod L)) hy, ?_⟩
    rcases Int.natAbs_eq_iff.mp h0 with h | h
    · left
      have := congrArg (fun z : ℤ => (z : ZMod L)) h
      push_cast at this
      linear_combination this
    · right
      have := congrArg (fun z : ℤ => (z : ZMod L)) h
      push_cast at this
      linear_combination this
  · have hx : x 0 = y 0 := by omega
    left
    refine ⟨by simpa using congrArg (fun z : ℤ => (z : ZMod L)) hx, ?_⟩
    rcases Int.natAbs_eq_iff.mp h1 with h | h
    · left
      have := congrArg (fun z : ℤ => (z : ZMod L)) h
      push_cast at this
      linear_combination this
    · right
      have := congrArg (fun z : ℤ => (z : ZMod L)) h
      push_cast at this
      linear_combination this


end StatMech.BeffaraDC
