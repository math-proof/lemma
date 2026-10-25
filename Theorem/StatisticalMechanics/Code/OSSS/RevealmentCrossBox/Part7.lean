/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentCrossBox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.TreeComplete.Part5
import Def.StatisticalMechanics.Code.OSSS.RevealmentCrossBox.Part6
open scoped BigOperators
open Finset
open StatMech.Lattice

set_option linter.style.longLine false


namespace StatMech

namespace OSSS

open StatMech.OSSS.DecisionTree

open StatMech.OSSS.Revealment

open StatMech.OSSS.RevealmentConstruction

open StatMech.OSSS.TreeComplete

open scoped Classical

variable {E : Type*} [Fintype E] [DecidableEq E]

variable {V : Type*} [DecidableEq V]


omit [Fintype E] in

theorem eval_crossTree (endU endV : E → V) (o : V) (C : Set V)
    (l : List E) (disc₀ : Finset V) (ω : ConfigSpace E) :
    (crossTree endU endV o C l disc₀).eval ω
      = decide (∃ y ∈ ((xbPass endU endV o ω l)^[xbCount endU endV o l disc₀]
          (disc₀, ∅)).2, y ∈ C) := by
  unfold crossTree
  rw [eval_buildTree]
  congr 1
  rw [xbCount]
  exact (runState_repeatList_xb endU endV o ω l _ (disc₀, ∅)).symm ▸ rfl


omit [Fintype E] in


theorem eval_crossTree_iff (endU endV : E → V) (o : V) (B C : Set V)
    (l : List E) (hl : ∀ e, e ∈ l) (disc₀ : Finset V)
    (hBdisc : ∀ b ∈ B, b ∈ disc₀) (hoB : o ∉ disc₀)
    (hcross : ∀ ω, ConnOpenSet endU endV ω o C → ConnOpenSet endU endV ω o B)
    (ω : ConfigSpace E) :
    (crossTree endU endV o C l disc₀).eval ω = true ↔ ConnOpenSet endU endV ω o C := by
  rw [eval_crossTree, decide_eq_true_eq]
  set N := xbCount endU endV o l disc₀ with hN
  set s := (xbPass endU endV o ω l)^[N] (disc₀, ∅) with hs
  have hfix : xbPass endU endV o ω l s = s := xbPass_fixpoint endU endV o ω l disc₀
  have hrun : runState (xbGuard endU endV) (xbStep endU endV o) ω (repeatList l N) (disc₀, ∅) = s := by
    rw [runState_repeatList_xb]
  have hfix1 : runState (geomGuard endU endV) (geomStep endU endV) ω l s.1 = s.1 := by
    have hc := congrArg Prod.fst hfix
    rwa [xbPass, fst_runState_xbStep] at hc
  have hsub : s.2 ⊆ s.1 := by
    rw [← hrun]; exact snd_sub_fst_runState endU endV o ω (repeatList l N) (disc₀, ∅) (by simp)
  constructor
  · rintro ⟨y, hyD0, hyC⟩
    have hr0 : reach0Inv endU endV ω o s := by
      rw [← hrun]
      exact reach0Inv_runState endU endV ω o (repeatList l N) (disc₀, ∅) (by intro x hx; simp at hx)
    exact ⟨y, hyC, reachOpen_symm (hr0 y hyD0)⟩
  · intro hoC
    obtain ⟨b, hbC, hreach⟩ := hoC
    have hoB' : ConnOpenSet endU endV ω o B := hcross ω ⟨b, hbC, hreach⟩
    have hsat1 : Saturated endU endV ω l s.1 := saturated_of_fixpoint endU endV ω l s.1 hfix1
    have hdisc_sub : disc₀ ⊆ s.1 := by
      rw [← hrun, fst_runState_xbStep]
      exact subset_runState endU endV ω (repeatList l N) disc₀
    obtain ⟨bB, hbBB, hreachB⟩ := hoB'
    have hoD : o ∈ s.1 :=
      mem_of_reachOpen_of_saturated endU endV ω l s.1 hsat1 hl hreachB
        (hdisc_sub (hBdisc bB hbBB))
    have hseed : oSeedInv o s := by
      rw [← hrun]
      exact oSeedInv_runState endU endV o ω (repeatList l N) (disc₀, ∅)
        (by intro h; exact absurd (by simpa using h) hoB)
    have hoD0 : o ∈ s.2 := hseed hoD
    have hsat2 : Saturated endU endV ω l s.2 :=
      snd_saturated_of_fixpoint endU endV o ω l s hsub hfix
    have hbD0 : b ∈ s.2 :=
      mem_of_reachOpen_of_saturated endU endV ω l s.2 hsat2 hl (reachOpen_symm hreach) hoD0
    exact ⟨b, hbD0, hbC⟩

omit [Fintype E] in


theorem evalR_crossTree (endU endV : E → V) (o : V) (B C : Set V)
    (l : List E) (hl : ∀ e, e ∈ l) (disc₀ : Finset V)
    (hBdisc : ∀ b ∈ B, b ∈ disc₀) (hoB : o ∉ disc₀)
    (hcross : ∀ ω, ConnOpenSet endU endV ω o C → ConnOpenSet endU endV ω o B)
    (ω : ConfigSpace E) [Decidable (ConnOpenSet endU endV ω o C)] :
    (crossTree endU endV o C l disc₀).evalR ω
      = if ConnOpenSet endU endV ω o C then (1 : ℝ) else 0 := by
  unfold DecisionTree.evalR
  by_cases hconn : ConnOpenSet endU endV ω o C
  · rw [if_pos ((eval_crossTree_iff endU endV o B C l hl disc₀ hBdisc hoB hcross ω).mpr hconn),
      if_pos hconn]
  · have heval : (crossTree endU endV o C l disc₀).eval ω ≠ true :=
      fun h => hconn ((eval_crossTree_iff endU endV o B C l hl disc₀ hBdisc hoB hcross ω).mp h)
    rw [if_neg heval, if_neg hconn]


omit [Fintype E] in


theorem queried_crossTree_imp (endU endV : E → V) (o : V) (B C : Set V)
    (l : List E) (disc₀ : Finset V) (hdisc₀ : ∀ x ∈ disc₀, x ∈ B) (ω : ConfigSpace E) (i : E)
    (hi : i ∈ (crossTree endU endV o C l disc₀).queried ω) :
    ConnOpenSet endU endV ω (endU i) B ∨ ConnOpenSet endU endV ω (endV i) B := by
  
  have hInv0 : geomInv endU endV ω B (disc₀, (∅ : Finset V)).1 :=
    fun x hx => connOpenSet_of_mem (hdisc₀ x hx)
  obtain ⟨τ, hτInv, hτg⟩ := mem_queried_buildTree (guard := xbGuard endU endV)
    (step := xbStep endU endV o)
    (base := fun s => decide (∃ y ∈ s.2, y ∈ C))
    (Inv := fun s => geomInv endU endV ω B s.1) (ω := ω)
    (fun σ e hσ hg => by
      
      have hg1 : geomGuard endU endV σ.1 e = true := hg
      have := geomInv_step endU endV ω B σ.1 e hσ hg1
      rwa [← fst_xbStep endU endV o σ e (ω e)] at this)
    (repeatList l (xbCount endU endV o l disc₀)) (disc₀, ∅) hInv0 i hi
  have hτg' : geomGuard endU endV τ.1 i = true := hτg
  unfold geomGuard at hτg'; simp only [decide_eq_true_eq] at hτg'
  rcases hτg' with hU | hV
  · exact Or.inl (hτInv _ hU)
  · exact Or.inr (hτInv _ hV)


theorem reveal_crossTree_le {ν : E → Bool → ℝ} (hν : IsProbWeight ν)
    (endU endV : E → V) (o : V) (B C : Set V) (l : List E) (disc₀ : Finset V)
    (hdisc₀ : ∀ x ∈ disc₀, x ∈ B) (i : E) :
    reveal ν (crossTree endU endV o C l disc₀) i
      ≤ expect ν (fun ω => if ConnOpenSet endU endV ω (endU i) B then (1 : ℝ) else 0)
        + expect ν (fun ω => if ConnOpenSet endU endV ω (endV i) B then (1 : ℝ) else 0) := by
  have h := revealment_le_of_queried_imp_or hν (crossTree endU endV o C l disc₀) i
    (fun ω => ConnOpenSet endU endV ω (endU i) B)
    (fun ω => ConnOpenSet endU endV ω (endV i) B)
    (fun ω hq => queried_crossTree_imp endU endV o B C l disc₀ hdisc₀ ω i hq)
  rwa [Revealment.revealment] at h


section Lattice

variable {d : ℕ}


theorem evalR_crossTree_connected
    {edge : E → Sym2 (Site d)} (hinj : Function.Injective edge)
    {endU endV : E → Site d} (hcoh : ∀ e, edge e = s(endU e, endV e))
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    (k n : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n)
    (o : Site d) (ho : o ∈ box d (k - 1))
    (l : List E) (hl : ∀ e, e ∈ l) (disc₀ : Finset (Site d))
    (hBdisc : ∀ b ∈ vertexBoundary d k, b ∈ disc₀) (hoB : o ∉ disc₀)
    (ω : ConfigSpace E)
    [Decidable (ConnectedToSet d (liftCfg edge ω) o (vertexBoundary d n))] :
    (crossTree endU endV o (vertexBoundary d n) l disc₀).evalR ω
      = if ConnectedToSet d (liftCfg edge ω) o (vertexBoundary d n) then (1 : ℝ) else 0 := by
  have hcross : ∀ ω', ConnOpenSet endU endV ω' o (vertexBoundary d n)
      → ConnOpenSet endU endV ω' o (vertexBoundary d k) :=
    fun ω' h => connOpenSet_boundary_mono hk hkn hadj ho h
  unfold DecisionTree.evalR
  by_cases hconn : ConnectedToSet d (liftCfg edge ω) o (vertexBoundary d n)
  · have hopenconn : ConnOpenSet endU endV ω o (vertexBoundary d n) :=
      connectedToSet_imp_connOpenSet hcoh hconn
    rw [if_pos ((eval_crossTree_iff endU endV o (vertexBoundary d k) (vertexBoundary d n)
        l hl disc₀ hBdisc hoB hcross ω).mpr hopenconn), if_pos hconn]
  · have heval : (crossTree endU endV o (vertexBoundary d n) l disc₀).eval ω ≠ true := by
      intro h
      have hopenconn := (eval_crossTree_iff endU endV o (vertexBoundary d k) (vertexBoundary d n)
        l hl disc₀ hBdisc hoB hcross ω).mp h
      exact hconn (connOpenSet_imp_connectedToSet hinj hcoh hadj hopenconn)
    rw [if_neg heval, if_neg hconn]


theorem reveal_crossTree_le_connected {ν : E → Bool → ℝ} (hν : IsProbWeight ν)
    {edge : E → Sym2 (Site d)} (hinj : Function.Injective edge)
    {endU endV : E → Site d} (hcoh : ∀ e, edge e = s(endU e, endV e))
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    (o : Site d) (C : Set (Site d)) (k : ℕ) (l : List E) (disc₀ : Finset (Site d))
    (hdisc₀ : ∀ x ∈ disc₀, x ∈ vertexBoundary d k) (i : E) :
    reveal ν (crossTree endU endV o C l disc₀) i
      ≤ expect ν (fun ω => if ConnectedToSet d (liftCfg edge ω) (endU i) (vertexBoundary d k) then (1 : ℝ) else 0)
        + expect ν (fun ω => if ConnectedToSet d (liftCfg edge ω) (endV i) (vertexBoundary d k) then (1 : ℝ) else 0) := by
  refine le_trans
    (reveal_crossTree_le hν endU endV o (vertexBoundary d k) C l disc₀ hdisc₀ i) ?_
  apply add_le_add
  · exact expect_indicator_mono hν _ _
      (fun ω hP => connOpenSet_imp_connectedToSet hinj hcoh hadj hP)
  · exact expect_indicator_mono hν _ _
      (fun ω hP => connOpenSet_imp_connectedToSet hinj hcoh hadj hP)

end Lattice
end OSSS
end StatMech
