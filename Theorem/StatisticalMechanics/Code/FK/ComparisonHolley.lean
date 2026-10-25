/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ComparisonHolley.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.Comparison
import Theorem.StatisticalMechanics.Code.FK.FiniteEnergy.Part4
import Theorem.StatisticalMechanics.Code.FK.HolleyCoupling.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.FKG
import Theorem.StatisticalMechanics.Code.Inequalities.Pivotal.Part2
import Theorem.StatisticalMechanics.Code.Foundations.StochasticDomination
import Def.StatisticalMechanics.Code.FK.ComparisonHolley
open scoped BigOperators
open MeasureTheory

set_option linter.unusedSectionVars false


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

open StatMech


theorem numClusters_antitone {a a' : ConfigSpace (Sym2 V)} (h : a ≤ a') :
    numClusters G a' ≤ numClusters G a := by
  simp only [numClusters_eq_finrank]
  apply Submodule.finrank_mono
  intro x hx
  rw [mem_kerLap] at hx ⊢
  intro i j hij
  apply hx
  rw [openSub_adj] at hij ⊢
  refine ⟨hij.1, ?_⟩
  have hb : a s(i, j) ≤ a' s(i, j) := h s(i, j)
  rw [hij.2] at hb
  exact le_antisymm (by simp) hb


theorem numClusters_setOpen_succ_of_closed {b : ConfigSpace (Sym2 V)} {e : Sym2 V}
    (hclosed : b e = false) :
    numClusters G b ≤ numClusters G (setOpen e b) + 1 := by
  have hkey := numClusters_setClosed_le_setOpen_succ G e (setOpen e b)
  rw [setClosed_setOpen, setOpen_setOpen] at hkey
  have hb : setClosed e b = b := by
    funext e'
    by_cases h : e' = e
    · rw [h, setClosed_self, hclosed]
    · rw [setClosed_of_ne h]
  rwa [hb] at hkey


theorem openCount_setOpen_of_closed {ω : ConfigSpace (Sym2 V)} {e : Sym2 V}
    (he : e ∈ G.edgeFinset) (hclosed : ω e = false) :
    chOpenCount G (setOpen e ω) = chOpenCount G ω + 1 := by
  unfold chOpenCount
  have hset : G.edgeFinset.filter (fun e' => setOpen e ω e' = true)
      = insert e (G.edgeFinset.filter (fun e' => ω e' = true)) := by
    ext e'
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hmem, hval⟩
      by_cases h : e' = e
      · exact Or.inl h
      · rw [setOpen_of_ne h] at hval; exact Or.inr ⟨hmem, hval⟩
    · rintro (h | ⟨hmem, hval⟩)
      · exact ⟨h ▸ he, by rw [h]; exact setOpen_self e ω⟩
      · refine ⟨hmem, ?_⟩
        by_cases h : e' = e
        · rw [h]; exact setOpen_self e ω
        · rw [setOpen_of_ne h]; exact hval
  rw [hset, Finset.card_insert_of_notMem]
  rw [Finset.mem_filter]
  rintro ⟨_, hval⟩
  rw [hclosed] at hval
  exact Bool.noConfusion hval


end FK
end StatMech
