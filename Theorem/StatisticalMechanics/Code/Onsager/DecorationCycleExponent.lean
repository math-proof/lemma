/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationCycleExponent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationLoopClassification.Part5
import Mathlib.Combinatorics.SimpleGraph.Acyclic


namespace StatMech.Onsager

open Finset SimpleGraph

theorem ons_portLine_isTree : (SimpleGraph.pathGraph 4).IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  constructor
  · simpa using SimpleGraph.pathGraph_connected 3
  · rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card,
      Nat.card_eq_fintype_card]
    have hedges : (SimpleGraph.pathGraph 4).edgeFinset =
        {s((0 : Fin 4), (1 : Fin 4)), s((1 : Fin 4), (2 : Fin 4)),
          s((2 : Fin 4), (3 : Fin 4))} := by
      ext edge
      induction edge using Sym2.inductionOn with
      | _ u v =>
          fin_cases u <;> fin_cases v <;>
            simp [SimpleGraph.mem_edgeFinset,
              SimpleGraph.pathGraph_adj, Sym2.eq_iff]
    rw [hedges]
    decide


theorem ons_internalPath_unique
    {L : ℕ} (site : ZMod L × ZMod L) (a b : Fin 4)
    (p q : (ons_decGraph L).Walk (site, a) (site, b))
    (hpint : ∀ d ∈ p.darts, ons_decInternalAdj d.fst d.snd)
    (hqint : ∀ d ∈ q.darts, ons_decInternalAdj d.fst d.snd)
    (hp : p.IsPath) (hq : q.IsPath) :
    p = q := by
  let pp := p.support.map (fun x ↦ x.2)
  let qq := q.support.map (fun x ↦ x.2)
  have hppne : pp ≠ [] := by simp [pp]
  have hqqne : qq ≠ [] := by simp [qq]
  have hppchain : List.IsChain (SimpleGraph.pathGraph 4).Adj pp := by
    apply (ons_support_directions_isChain_portLine p hpint).imp
    intro x y hxy
    rw [SimpleGraph.pathGraph_adj]
    exact hxy
  have hqqchain : List.IsChain (SimpleGraph.pathGraph 4).Adj qq := by
    apply (ons_support_directions_isChain_portLine q hqint).imp
    intro x y hxy
    rw [SimpleGraph.pathGraph_adj]
    exact hxy
  have hpsite := ons_internalWalk_support_site p hpint
  have hqsite := ons_internalWalk_support_site q hqint
  have hppnodup : pp.Nodup := by
    apply hp.support_nodup.map_on
    intro x hx y hy hxy
    apply Prod.ext
    · exact (hpsite x hx).trans (hpsite y hy).symm
    · exact hxy
  have hqqnodup : qq.Nodup := by
    apply hq.support_nodup.map_on
    intro x hx y hy hxy
    apply Prod.ext
    · exact (hqsite x hx).trans (hqsite y hy).symm
    · exact hxy
  let ppWalk : (SimpleGraph.pathGraph 4).Walk a b :=
    (SimpleGraph.Walk.ofSupport pp hppne hppchain).copy
      (by simp [pp]) (by simp [pp])
  let qqWalk : (SimpleGraph.pathGraph 4).Walk a b :=
    (SimpleGraph.Walk.ofSupport qq hqqne hqqchain).copy
      (by simp [qq]) (by simp [qq])
  have hppath : ppWalk.IsPath := by
    rw [SimpleGraph.Walk.isPath_def]
    simpa [ppWalk] using hppnodup
  have hqpath : qqWalk.IsPath := by
    rw [SimpleGraph.Walk.isPath_def]
    simpa [qqWalk] using hqqnodup
  have hwalk : ppWalk = qqWalk := by
    exact congrArg Subtype.val
      (ons_portLine_isTree.isAcyclic.path_unique
        ⟨ppWalk, hppath⟩ ⟨qqWalk, hqpath⟩)
  have hports : pp = qq := by
    have hs := congrArg SimpleGraph.Walk.support hwalk
    simpa [ppWalk, qqWalk] using hs
  apply SimpleGraph.Walk.ext_support
  calc
    p.support = pp.map (fun mu ↦ (site, mu)) := by
      change p.support =
        (p.support.map (fun x ↦ x.2)).map (fun mu ↦ (site, mu))
      rw [List.map_map]
      symm
      calc
        p.support.map (fun x ↦ (site, x.2)) =
            p.support.map id := by
          apply List.map_congr_left
          intro x hx
          apply Prod.ext
          · exact (hpsite x hx).symm
          · rfl
        _ = p.support := List.map_id _
    _ = qq.map (fun mu ↦ (site, mu)) := by rw [hports]
    _ = q.support := by
      change (q.support.map (fun x ↦ x.2)).map
          (fun mu ↦ (site, mu)) = q.support
      rw [List.map_map]
      calc
        q.support.map (fun x ↦ (site, x.2)) =
            q.support.map id := by
          apply List.map_congr_left
          intro x hx
          apply Prod.ext
          · exact (hqsite x hx).symm
          · rfl
        _ = q.support := List.map_id _

theorem ons_decPortChainPath_internal
    (L : ℕ) [Fact (2 < L)] (site : ZMod L × ZMod L)
    (a b : Fin 4) :
    ∀ d ∈ (ons_decPortChainPath L site a b).darts,
      ons_decInternalAdj d.fst d.snd := by
  intro d hd
  have hadj := d.adj
  change ons_decAdj L d.fst d.snd at hadj
  rcases hadj with hext | hint
  · have hdmem : d.fst ∈
        ons_decWalkExternalDarts (ons_decPortChainPath L site a b) := by
      unfold ons_decWalkExternalDarts
      apply List.mem_map.mpr
      refine ⟨d, List.mem_filter.mpr ⟨hd, ?_⟩, rfl⟩
      simpa [ons_decDartIsExternal] using hext
    rw [ons_decPortChainPath_externalDarts_eq_nil] at hdmem
    exact (by simpa using hdmem : False).elim
  · exact hint


theorem ons_internalPath_eq_decPortChainPath
    (L : ℕ) [Fact (2 < L)] (source target : ons_Dart L)
    (hstep : target.1 = ons_dirStep L source.2 source.1)
    (p : (ons_decGraph L).Walk (ons_dartRev L source) target)
    (hpint : ∀ d ∈ p.darts, ons_decInternalAdj d.fst d.snd)
    (hp : p.IsPath) :
    p = (ons_decPortChainPath L target.1 (source.2 + 2) target.2).copy
      (by
        apply Prod.ext
        · exact hstep.trans (ons_dartRev_fst_eq_step L source).symm
        · simp [ons_dartRev]) rfl := by
  have hstart : (target.1, source.2 + 2) = ons_dartRev L source := by
    apply Prod.ext
    · exact hstep.trans (ons_dartRev_fst_eq_step L source).symm
    · simp [ons_dartRev]
  let chain := ons_decPortChainPath L target.1 (source.2 + 2) target.2
  let p' : (ons_decGraph L).Walk
      (target.1, source.2 + 2) target := p.copy hstart.symm rfl
  have hp'int : ∀ d ∈ p'.darts,
      ons_decInternalAdj d.fst d.snd := by
    intro d hd
    apply hpint d
    simpa [p'] using hd
  have hp' : p'.IsPath := by
    exact (SimpleGraph.Walk.isPath_copy p hstart.symm rfl).mpr hp
  have heq : p' = chain :=
    ons_internalPath_unique target.1 (source.2 + 2) target.2
      p' chain hp'int
      (ons_decPortChainPath_internal L target.1
        (source.2 + 2) target.2)
      hp' (ons_decPortChainPath_isPath L target.1
        (source.2 + 2) target.2)
  apply SimpleGraph.Walk.ext_support
  have hs := congrArg SimpleGraph.Walk.support heq
  simpa [p', chain] using hs

end StatMech.Onsager
