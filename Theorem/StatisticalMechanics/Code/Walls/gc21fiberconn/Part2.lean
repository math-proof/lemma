/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc21fiberconn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc20closure.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc19switching.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc18core.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc16core.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc7core
import Theorem.StatisticalMechanics.Code.Walls.gc6_munonneg
import Theorem.StatisticalMechanics.Code.Ising.TwoReplica.Part7
import Theorem.StatisticalMechanics.Code.Ising.TwoReplicaWeighted.Part2
import Theorem.StatisticalMechanics.Code.Ising.HdomNativeWeight.Part3
import Theorem.StatisticalMechanics.Code.Ising.AizenmanSignDominance.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Def.StatisticalMechanics.Code.Walls.gc21fiberconn.Part2
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Sharpness.RandomCurrent StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.FieldGhostDict


theorem gc21_posFibre_not_of_posFull_sourceless :
    (∀ e, gc21_k4 e ≤ gc21_m4 e)
      ∧ Ising.sources gc21_E4 gc21_k4 = (∅ : Finset (Fin 4))
      ∧ Ising.sources gc21_E4 gc21_m4 = ({0, 1, 2, 3} : Finset (Fin 4))
      ∧ connP (posEdges gc21_E4 gc21_m4) 0 3
      ∧ ¬ connP (posEdges gc21_E4 gc21_m4k) 0 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro e; unfold gc21_k4 gc21_m4; fin_cases e <;> simp_all
  · decide
  · decide
  · 
    refine Relation.ReflTransGen.single ⟨s(0, 3), ?_, by simp, by simp, by decide⟩
    rw [posEdges, Finset.mem_filter]
    refine ⟨by rw [gc21_E4]; simp, ?_⟩
    show 1 ≤ gc21_m4 s(0, 3)
    simp only [gc21_m4]; decide
  · 
    have hpos : posEdges gc21_E4 gc21_m4k = ({s(0, 1), s(2, 3)} : Finset (Sym2 (Fin 4))) := by
      decide
    intro h
    rw [hpos] at h
    have key : ∀ b : Fin 4, connP ({s(0, 1), s(2, 3)} : Finset (Sym2 (Fin 4))) 0 b →
        (b = 0 ∨ b = 1) := by
      intro b hb
      induction hb with
      | refl => left; rfl
      | tail _ hstep ih =>
        obtain ⟨e, he, ha, hbb, hne⟩ := hstep
        rw [Finset.mem_insert, Finset.mem_singleton] at he
        rcases ih with rfl | rfl <;> rcases he with rfl | rfl <;> simp_all
    rcases key 3 h with h3 | h3 <;> exact absurd h3 (by decide)


variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem gc21_fibre_posTrichotomy (m : ↥(withGhost G).edgeFinset → ℕ)
    (K₁ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e})
    (o x y g : Option V)
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hbdry : sources (withGhost G) (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))
        = ({o, x, y, g} : Finset (Option V))) :
    connP (posEdges (withGhost G).edgeFinset
          (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) o g
      ∨ (connP (posEdges (withGhost G).edgeFinset
            (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) o x
          ∧ connP (posEdges (withGhost G).edgeFinset
              (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) y g)
      ∨ (connP (posEdges (withGhost G).edgeFinset
            (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) o y
          ∧ connP (posEdges (withGhost G).edgeFinset
              (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) x g) := by
  set n : ↥(withGhost G).edgeFinset → ℕ := fun e => m e - K₁.1 e with hn
  have hnle : n ≤ m := fun e => by have := K₁.2 e; simp only [hn]; omega
  set S : Finset (FluxEdgeCopy.Copy (withGhost G) m) :=
    univ.filter (fun i : FluxEdgeCopy.Copy (withGhost G) m => i.2.val < n i.1) with hS
  have hprof : profileFlux (withGhost G) m S = n := profileFlux_surj (withGhost G) m n hnle
  have hconnK : ∀ a b, connK (endsM (withGhost G) m) S a b ↔
      connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) n)) a b := by
    intro a b
    rw [connK_iff, hprof, ← gc20_connP_posEdges_iff_currentConnected]
  have hSsrc : sources (endsM (withGhost G) m) S = ({o, x, y, g} : Finset (Option V)) := by
    rw [sources_eq, hprof]; exact hbdry
  have htri := gc7_core_pathCrossing_trichotomy_edgeCopy (withGhost G) m S o x y g
    hox hoy hog hxy hxg hyg hSsrc
  rcases htri with h | h | h
  · left; exact (hconnK o g).mp h
  · right; left; exact ⟨(hconnK o x).mp h.1, (hconnK y g).mp h.2⟩
  · right; right; exact ⟨(hconnK o y).mp h.1, (hconnK x g).mp h.2⟩


theorem gc21_fibre_oddArc_of_sourcePair (m : ↥(withGhost G).edgeFinset → ℕ)
    (K₁ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e}) {u v : Option V} (huv : u ≠ v)
    (hsrc : sources (withGhost G) (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e)) = {u, v}) :
    connP (oddEdges (withGhost G).edgeFinset
        (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) u v :=
  connOdd_of_sources (withGhost G).edgeFinset
    (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e)) (gc20_withGhost_loopless G) huv hsrc


theorem gc21_oddArc_imp_posArc (n : ↥(withGhost G).edgeFinset → ℕ) {u v : Option V}
    (hodd : connP (oddEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) n)) u v) :
    connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) n)) u v :=
  connOdd_imp_connPos (withGhost G).edgeFinset (ofEdgeFun (withGhost G) n) hodd


end StatMech.Walls
