/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTurnTransfer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.PeriodicTurnClosure.Part9
import Theorem.StatisticalMechanics.Code.Onsager.TorusPrimitiveWinding.Part3
import Def.StatisticalMechanics.Code.Onsager.DecorationTurnTransfer


namespace StatMech.Onsager

open StatMech.Onsager.BaseCase

open BigOperators

theorem ons_internalMicroDirections_turn
    (a : Fin 4) (ports : List (Fin 4))
    (hne : ports ≠ [])
    (hhead : ports.head? = some (a + 2))
    (hchain : List.IsChain ons_portLineAdj ports)
    (hnodup : ports.Nodup) :
    let dirs := List.replicate 4 a ++ ons_internalMicroDirections ports
    ons_openTurnSum dirs + ons_turnPow dirs.getLast! ports.getLast! =
      ons_turnPow a ports.getLast! := by
  cases ports with
  | nil => exact (hne rfl).elim
  | cons p₀ ps =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst p₀
      cases ps with
      | nil =>
          fin_cases a
          all_goals decide
      | cons p₁ ps =>
          cases ps with
          | nil =>
              simp only [List.isChain_cons_cons, List.IsChain.singleton,
                and_true] at hchain
              fin_cases a
              all_goals try fin_cases p₁
              all_goals
                first
                | decide
                | exfalso; revert hchain; decide
                | norm_num [ons_portLineAdj, Fin.add_def] at hchain
          | cons p₂ ps =>
              cases ps with
              | nil =>
                  simp only [List.isChain_cons_cons, List.IsChain.singleton,
                    and_true] at hchain
                  simp only [List.nodup_cons, List.mem_cons,
                    List.mem_singleton, not_or, not_false_eq_true,
                    and_true] at hnodup
                  fin_cases a
                  all_goals try fin_cases p₁
                  all_goals try fin_cases p₂
                  all_goals
                    first
                    | decide
                    | exfalso; revert hchain; decide
                    | exfalso; revert hnodup; decide
                    | norm_num [ons_portLineAdj, Fin.add_def] at hchain
                    | norm_num [Fin.add_def] at hnodup
              | cons p₃ ps =>
                  cases ps with
                  | nil =>
                      simp only [List.isChain_cons_cons,
                        List.IsChain.singleton, and_true] at hchain
                      simp only [List.nodup_cons, List.mem_cons,
                        List.mem_singleton, not_or, not_false_eq_true,
                        and_true] at hnodup
                      fin_cases a
                      all_goals try fin_cases p₁
                      all_goals try fin_cases p₂
                      all_goals try fin_cases p₃
                      all_goals
                        first
                        | decide
                        | exfalso; revert hchain; decide
                        | exfalso; revert hnodup; decide
                        | norm_num [ons_portLineAdj, Fin.add_def] at hchain
                        | norm_num [Fin.add_def] at hnodup
                  | cons p₄ ps =>
                      have hlen := hnodup.length_le_card
                      simp at hlen
                      omega

theorem ons_decEdgeMicroDarts_directions_external
    (L : ℕ) (d e : ons_Dart L)
    (hrev : e = ons_dartRev L d) :
    (ons_decEdgeMicroDarts L d e).map (fun a ↦ a.2) =
      List.replicate 4 d.2 := by
  subst e
  simp [ons_decEdgeMicroDarts, ons_decEdgeRouteDirs]

theorem ons_decEdgeMicroDarts_directions_internal
    (L : ℕ) (d e : ons_Dart L)
    (hint : ons_decInternalAdj d e) :
    (ons_decEdgeMicroDarts L d e).map (fun a ↦ a.2) =
      [e.2, e.2, d.2 + 2, d.2 + 2] := by
  rcases d with ⟨p, mu⟩
  rcases e with ⟨q, nu⟩
  have hpq : p = q := hint.1
  subst q
  fin_cases mu <;> fin_cases nu <;>
    simp [ons_decInternalAdj, ons_decEdgeMicroDarts,
      ons_decEdgeRouteDirs, ons_dartRev, ons_dirStep] at hint ⊢

theorem ons_walk_support_eq_cons
    {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) :
    p.support = u :: p.support.tail := by
  cases p <;> rfl

theorem ons_decExpanded_internal_directions
    (L : ℕ) [Fact (2 < L)] {u v : ons_Dart L}
    (p : (ons_decGraph L).Walk u v)
    (hint : ∀ a ∈ p.darts, ons_decInternalAdj a.fst a.snd) :
    (ons_decExpandedDartList L p).map (fun a ↦ a.2) =
      ons_internalMicroDirections (p.support.map (fun a ↦ a.2)) := by
  induction p with
  | nil => simp [ons_decExpandedDartList, ons_internalMicroDirections]
  | @cons u w v huw p ih =>
      have huw' : ons_decInternalAdj u w := by
        exact hint ⟨(u, w), huw⟩ (by simp)
      have htail : ∀ a ∈ p.darts,
          ons_decInternalAdj a.fst a.snd := by
        intro a ha
        exact hint a (by simp [ha])
      rw [ons_decExpandedDartList, SimpleGraph.Walk.darts_cons,
        List.flatMap_cons, List.map_append,
        ons_decEdgeMicroDarts_directions_internal L u w huw']
      have ih' := ih htail
      have hsupport := ons_walk_support_eq_cons p
      have hmap : w.2 :: p.support.tail.map (fun a ↦ a.2) =
          p.support.map (fun a ↦ a.2) := by
        simpa only [List.map_cons] using
          congrArg (List.map (fun a ↦ a.2)) hsupport.symm
      rw [SimpleGraph.Walk.support_cons, List.map_cons,
        hsupport, List.map_cons]
      rw [ons_internalMicroDirections]
      rw [hmap]
      exact congrArg
        (List.append [w.2, w.2, u.2 + 2, u.2 + 2]) ih'

theorem ons_support_directions_isChain_portLine
    {L : ℕ} {u v : ons_Dart L}
    (p : (ons_decGraph L).Walk u v)
    (hint : ∀ a ∈ p.darts, ons_decInternalAdj a.fst a.snd) :
    List.IsChain ons_portLineAdj (p.support.map (fun a ↦ a.2)) := by
  induction p with
  | nil => exact .singleton _
  | @cons u w v huw p ih =>
      rw [SimpleGraph.Walk.support_cons, List.map_cons]
      have hsupport := ons_walk_support_eq_cons p
      have hmap : w.2 :: p.support.tail.map (fun a ↦ a.2) =
          p.support.map (fun a ↦ a.2) := by
        simpa only [List.map_cons] using
          congrArg (List.map (fun a ↦ a.2)) hsupport.symm
      rw [hsupport, List.map_cons, List.isChain_cons_cons]
      constructor
      · have h := hint ⟨(u, w), huw⟩ (by simp)
        exact h.2
      · rw [hmap]
        apply ih
        intro a ha
        exact hint a (by simp [ha])

theorem ons_internalWalk_support_site
    {L : ℕ} {u v : ons_Dart L}
    (p : (ons_decGraph L).Walk u v)
    (hint : ∀ a ∈ p.darts, ons_decInternalAdj a.fst a.snd) :
    ∀ a ∈ p.support, a.1 = u.1 := by
  induction p with
  | nil => simp
  | @cons u w v huw p ih =>
      have huw' := hint ⟨(u, w), huw⟩ (by simp)
      have htail : ∀ a ∈ p.darts,
          ons_decInternalAdj a.fst a.snd := by
        intro a ha
        exact hint a (by simp [ha])
      intro a ha
      rw [SimpleGraph.Walk.support_cons, List.mem_cons] at ha
      rcases ha with rfl | ha
      · rfl
      · exact (ih htail a ha).trans huw'.1.symm

theorem ons_internalWalk_refined_turn
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    {v : ons_Dart L}
    (p : (ons_decGraph L).Walk (ons_dartRev L d) v)
    (hint : ∀ a ∈ p.darts, ons_decInternalAdj a.fst a.snd)
    (hpath : p.IsPath) :
    let dirs := List.replicate 4 d.2 ++
      (ons_decExpandedDartList L p).map (fun a ↦ a.2)
    ons_openTurnSum dirs + ons_turnPow dirs.getLast! v.2 =
      ons_turnPow d.2 v.2 := by
  let ports := p.support.map (fun a ↦ a.2)
  have hpne : ports ≠ [] := by simp [ports]
  have hphead : ports.head? = some (d.2 + 2) := by
    change (p.support.map (fun a ↦ a.2)).head? = _
    rw [ons_walk_support_eq_cons p, List.map_cons]
    simp [ons_dartRev]
  have hpchain : List.IsChain ons_portLineAdj ports :=
    ons_support_directions_isChain_portLine p hint
  have hpnodup : ports.Nodup := by
    rw [SimpleGraph.Walk.isPath_def] at hpath
    apply hpath.map_on
    intro a ha b hb hab
    have hsiteA := ons_internalWalk_support_site p hint a ha
    have hsiteB := ons_internalWalk_support_site p hint b hb
    exact Prod.ext (hsiteA.trans hsiteB.symm) hab
  have hplast : ports.getLast! = v.2 := by
    change (p.support.map (fun a ↦ a.2)).getLast! = _
    rw [ons_getLast!_eq_getLast ports hpne]
    rw [List.getLast_map]
    rw [p.getLast_support]
  rw [ons_decExpanded_internal_directions L p hint]
  have hturn := ons_internalMicroDirections_turn
    d.2 ports hpne hphead hpchain hpnodup
  rw [hplast] at hturn
  exact hturn

end StatMech.Onsager
