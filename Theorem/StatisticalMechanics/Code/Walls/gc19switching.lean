/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc19switching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc16core.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc7core
import Theorem.StatisticalMechanics.Code.Walls.gc6_munonneg
import Theorem.StatisticalMechanics.Code.Ising.HdomNativeWeight.Part3
import Theorem.StatisticalMechanics.Code.Ising.AizenmanSignDominance.Part2
import Theorem.StatisticalMechanics.Code.Ising.TwoReplicaWeighted.Part2
import Def.StatisticalMechanics.Code.Walls.gc19switching
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Sharpness.FieldGhostDict

open StatMech.Walls.Gc5EqGap StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (S : SimpleGraph V) [DecidableRel S.Adj]


lemma gc19_eref_le (p : ↥S.edgeFinset → ℕ) (P : Finset (Sym2 V)) {K : ↥S.edgeFinset → ℕ}
    (hK : ∀ e, K e ≤ p e) : ∀ e, gc19_eref S p P K e ≤ p e := by
  intro e; unfold gc19_eref
  by_cases h : (e.1 : Sym2 V) ∈ P
  · simp only [if_pos h]; omega
  · simp only [if_neg h]; exact hK e


lemma gc19_eref_involutive (p : ↥S.edgeFinset → ℕ) (P : Finset (Sym2 V)) {K : ↥S.edgeFinset → ℕ}
    (hK : ∀ e, K e ≤ p e) : gc19_eref S p P (gc19_eref S p P K) = K := by
  funext e; unfold gc19_eref
  by_cases h : (e.1 : Sym2 V) ∈ P
  · simp only [if_pos h]; have := hK e; omega
  · simp only [if_neg h]


lemma gc19_ofEdgeFun_eref (p K : ↥S.edgeFinset → ℕ) (P : Finset (Sym2 V)) :
    ofEdgeFun S (gc19_eref S p P K)
      = StatMech.Ising.reflect (ofEdgeFun S p) P (ofEdgeFun S K) := by
  funext e
  unfold gc19_eref StatMech.Ising.reflect ofEdgeFun
  by_cases he : e ∈ S.edgeFinset
  · by_cases hP : e ∈ P <;> simp [he, hP]
  · by_cases hP : e ∈ P <;> simp [he, hP]


end StatMech.Walls
