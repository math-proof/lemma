/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSLebowitz.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GHSDuplicateVariable.Part4
import Theorem.StatisticalMechanics.Code.Ising.GHSVertexPartition.Part8
import Theorem.StatisticalMechanics.Code.Inequalities.FKG
import Def.StatisticalMechanics.Code.Ising.GHSLebowitz.Part5
open scoped BigOperators symmDiff
open Finset SimpleGraph Set

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000


namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem ghsLTComplete_eq_on (q a : ConfigSpace V) {v : V} (hv : q v = true) :
    ghsLTComplete q (ghsLSplitEquiv q a).1 v = a v := by
  simp [ghsLTComplete, ghsLSplitEquiv, hv]

theorem ghsLUComplete_eq_on (q a : ConfigSpace V) {v : V} (hv : ¬ q v = true) :
    ghsLUComplete q (ghsLSplitEquiv q a).2 v = a v := by
  simp [ghsLUComplete, ghsLSplitEquiv, hv]


theorem ghsLTWeight_split (β h : ℝ) (q a : ConfigSpace V) :
    ghsLTWeight G β h q a =
      ghsLTWeight G β h q (ghsLTComplete q (ghsLSplitEquiv q a).1) := by
  unfold ghsLTWeight
  have hb :
      (∑ e ∈ ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q), bond a e) =
        ∑ e ∈ ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q),
          bond (ghsLTComplete q (ghsLSplitEquiv q a).1) e := by
    apply Finset.sum_congr rfl
    intro e he
    have hi := (Finset.mem_filter.mp he).2
    induction e with
    | h x y =>
        have hx : q x = true := mem_ghsLAgreeFinset q x |>.mp (hi x (by simp))
        have hy : q y = true := mem_ghsLAgreeFinset q y |>.mp (hi y (by simp))
        simp only [bond_mk]
        rw [show spin (ghsLTComplete q (ghsLSplitEquiv q a).1) x = spin a x by
          unfold spin; rw [ghsLTComplete_eq_on q a hx]]
        rw [show spin (ghsLTComplete q (ghsLSplitEquiv q a).1) y = spin a y by
          unfold spin; rw [ghsLTComplete_eq_on q a hy]]
  have hs : (∑ v ∈ ghsLAgreeFinset q, spin a v) =
      ∑ v ∈ ghsLAgreeFinset q, spin (ghsLTComplete q (ghsLSplitEquiv q a).1) v := by
    apply Finset.sum_congr rfl
    intro v hv
    have hq := (mem_ghsLAgreeFinset q v).mp hv
    unfold spin
    rw [ghsLTComplete_eq_on q a hq]
  rw [hb, hs]


theorem ghsLUWeight_split (β : ℝ) (q a : ConfigSpace V) :
    ghsLUWeight G β q a =
      ghsLUWeight G β q (ghsLUComplete q (ghsLSplitEquiv q a).2) := by
  unfold ghsLUWeight
  congr 2
  · apply Finset.sum_congr rfl
    intro e he
    have hi := (Finset.mem_filter.mp he).2
    induction e with
    | h x y =>
        have hx : ¬ q x = true := by
          simpa using (Finset.mem_compl.mp (hi x (by simp)))
        have hy : ¬ q y = true := by
          simpa using (Finset.mem_compl.mp (hi y (by simp)))
        simp only [bond_mk]
        rw [show spin (ghsLUComplete q (ghsLSplitEquiv q a).2) x = spin a x by
          unfold spin; rw [ghsLUComplete_eq_on q a hx]]
        rw [show spin (ghsLUComplete q (ghsLSplitEquiv q a).2) y = spin a y by
          unfold spin; rw [ghsLUComplete_eq_on q a hy]]


theorem ghsL_tvar_split (q a : ConfigSpace V) (y : V) :
    tvar a (ghsLMate q a) y =
      tvar (ghsLTComplete q (ghsLSplitEquiv q a).1)
        (ghsLMate q (ghsLTComplete q (ghsLSplitEquiv q a).1)) y := by
  rw [ghsL_tvar_mate, ghsL_tvar_mate]
  by_cases hy : q y
  · simp only [if_pos hy]
    unfold spin
    rw [ghsLTComplete_eq_on q a hy]
  · simp [hy]


theorem ghsL_uvar_mul_split (q a : ConfigSpace V) (o x : V) :
    uvar a (ghsLMate q a) o * uvar a (ghsLMate q a) x =
      uvar (ghsLUComplete q (ghsLSplitEquiv q a).2)
          (ghsLMate q (ghsLUComplete q (ghsLSplitEquiv q a).2)) o *
        uvar (ghsLUComplete q (ghsLSplitEquiv q a).2)
          (ghsLMate q (ghsLUComplete q (ghsLSplitEquiv q a).2)) x := by
  simp only [ghsL_uvar_mate]
  by_cases ho : q o <;> by_cases hx : q x
  · simp [ho]
  · simp [ho]
  · simp [hx]
  · simp only [if_neg ho, if_neg hx]
    congr 1 <;> unfold spin
    · rw [ghsLUComplete_eq_on q a ho]
    · rw [ghsLUComplete_eq_on q a hx]


end Ising
end StatMech
