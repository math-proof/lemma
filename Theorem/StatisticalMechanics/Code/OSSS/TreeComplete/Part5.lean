/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TreeComplete.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.OSSS.RevealmentConstruction.Part7
import Def.StatisticalMechanics.Code.OSSS.TreeComplete.Part4
open scoped BigOperators
open Finset
open StatMech.Lattice

set_option linter.style.longLine false


namespace StatMech

namespace OSSS

namespace TreeComplete

open StatMech.OSSS

open StatMech.OSSS.DecisionTree

open StatMech.OSSS.Revealment

open StatMech.OSSS.RevealmentConstruction

open scoped Classical

variable {E : Type*} [Fintype E] [DecidableEq E]

variable {V : Type*} [DecidableEq V]

omit [Fintype E] in


theorem eval_completeTree_iff (endU endV : E → V) (o : V) (B : Set V)
    (l : List E) (hl : ∀ e, e ∈ l) (disc₀ : Finset V)
    (hdisc₀ : ∀ x ∈ disc₀, x ∈ B) (hBdisc : ∀ b ∈ B, b ∈ disc₀) (ω : ConfigSpace E) :
    (completeTree endU endV o l disc₀).eval ω = true ↔ ConnOpenSet endU endV ω o B := by
  constructor
  · intro h
    exact eval_exploreTree_imp_conn endU endV o B _ disc₀ hdisc₀ ω h
  · intro h
    
    unfold completeTree exploreTree
    rw [eval_buildTree]
    simp only [decide_eq_true_eq]
    exact mem_runState_repeatList_of_connOpenSet endU endV ω l hl B disc₀ hBdisc h

omit [Fintype E] in


theorem evalR_completeTree (endU endV : E → V) (o : V) (B : Set V)
    (l : List E) (hl : ∀ e, e ∈ l) (disc₀ : Finset V)
    (hdisc₀ : ∀ x ∈ disc₀, x ∈ B) (hBdisc : ∀ b ∈ B, b ∈ disc₀) (ω : ConfigSpace E)
    [Decidable (ConnOpenSet endU endV ω o B)] :
    (completeTree endU endV o l disc₀).evalR ω
      = if ConnOpenSet endU endV ω o B then (1 : ℝ) else 0 := by
  unfold DecisionTree.evalR
  by_cases hconn : ConnOpenSet endU endV ω o B
  · rw [if_pos ((eval_completeTree_iff endU endV o B l hl disc₀ hdisc₀ hBdisc ω).mpr hconn),
      if_pos hconn]
  · have heval : (completeTree endU endV o l disc₀).eval ω ≠ true :=
      fun h => hconn ((eval_completeTree_iff endU endV o B l hl disc₀ hdisc₀ hBdisc ω).mp h)
    rw [if_neg heval, if_neg hconn]


section Lattice

variable {d : ℕ}

omit [DecidableEq E] in


theorem exists_abstract_open_edge {edge : E → Sym2 (Site d)} {endU endV : E → Site d}
    {ω : ConfigSpace E} (hcoh : ∀ e, edge e = s(endU e, endV e))
    {u v : Site d} (hopen : liftCfg edge ω s(u, v) = true) :
    ∃ e, ω e = true ∧ ((endU e = u ∧ endV e = v) ∨ (endU e = v ∧ endV e = u)) := by
  unfold liftCfg at hopen
  by_cases hex : ∃ e, edge e = s(u, v)
  · rw [dif_pos hex] at hopen
    refine ⟨hex.choose, hopen, ?_⟩
    have hch : edge hex.choose = s(u, v) := hex.choose_spec
    rw [hcoh hex.choose, Sym2.eq_iff] at hch; exact hch
  · rw [dif_neg hex] at hopen; exact absurd hopen (by simp)

omit [DecidableEq E] in


theorem connected_imp_reachOpen {edge : E → Sym2 (Site d)} {endU endV : E → Site d}
    {ω : ConfigSpace E} (hcoh : ∀ e, edge e = s(endU e, endV e))
    {x y : Site d} (h : Connected d (liftCfg edge ω) x y) :
    ReachOpen endU endV ω x y := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact ReachOpen.refl _
  | @cons a b c hadj p ih =>
      have hopen : liftCfg edge ω s(a, b) = true := hadj.2
      obtain ⟨e, hωe, hpair⟩ := exists_abstract_open_edge hcoh hopen
      exact ReachOpen.step e hωe hpair ih

omit [DecidableEq E] in


theorem connectedToSet_imp_connOpenSet {edge : E → Sym2 (Site d)} {endU endV : E → Site d}
    (hcoh : ∀ e, edge e = s(endU e, endV e)) {ω : ConfigSpace E} {x : Site d} {B : Set (Site d)}
    (h : ConnectedToSet d (liftCfg edge ω) x B) : ConnOpenSet endU endV ω x B := by
  obtain ⟨b, hbB, hconn⟩ := h
  exact ⟨b, hbB, connected_imp_reachOpen hcoh hconn⟩


theorem evalR_completeTree_connected {edge : E → Sym2 (Site d)}
    (hinj : Function.Injective edge) {endU endV : E → Site d}
    (hcoh : ∀ e, edge e = s(endU e, endV e))
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    (o : Site d) (B : Set (Site d)) (l : List E) (hl : ∀ e, e ∈ l) (disc₀ : Finset (Site d))
    (hdisc₀ : ∀ x ∈ disc₀, x ∈ B) (hBdisc : ∀ b ∈ B, b ∈ disc₀) (ω : ConfigSpace E)
    [Decidable (ConnectedToSet d (liftCfg edge ω) o B)] :
    (completeTree endU endV o l disc₀).evalR ω
      = if ConnectedToSet d (liftCfg edge ω) o B then (1 : ℝ) else 0 := by
  unfold DecisionTree.evalR
  by_cases hconn : ConnectedToSet d (liftCfg edge ω) o B
  · have hopenconn : ConnOpenSet endU endV ω o B := connectedToSet_imp_connOpenSet hcoh hconn
    rw [if_pos ((eval_completeTree_iff endU endV o B l hl disc₀ hdisc₀ hBdisc ω).mpr hopenconn),
      if_pos hconn]
  · have heval : (completeTree endU endV o l disc₀).eval ω ≠ true := by
      intro h
      have hopenconn := (eval_completeTree_iff endU endV o B l hl disc₀ hdisc₀ hBdisc ω).mp h
      exact hconn (connOpenSet_imp_connectedToSet hinj hcoh hadj hopenconn)
    rw [if_neg heval, if_neg hconn]

end Lattice
end TreeComplete
end OSSS
end StatMech
