/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABGhostRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.ABFiniteAssembly.Part2
import Def.StatisticalMechanics.Code.Sharpness.ABGhostRegularity.Part2
open Filter Finset Set SimpleGraph Topology
open Asymptotics


namespace StatMech

namespace Sharpness

open ConfigSpace

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


@[simp] theorem abgrKeepGhost_chosen (x : V) (omega : ConfigSpace (Sym2 (Option V))) :
    abgrKeepGhost x omega s(some x, none) = omega s(some x, none) := by
  simp [abgrKeepGhost]

@[simp] theorem abgrKeepGhost_physical (x a b : V)
    (omega : ConfigSpace (Sym2 (Option V))) :
    abgrKeepGhost x omega s(some a, some b) = omega s(some a, some b) := by
  simp [abgrKeepGhost, FieldGhostDict.ghostEdges, Sym2.eq_iff]

theorem abgrKeepGhost_le (x : V) (omega : ConfigSpace (Sym2 (Option V))) :
    abgrKeepGhost x omega <= omega := by
  intro e
  unfold abgrKeepGhost
  split_ifs <;> simp_all

@[simp] theorem abgrCloseGhost_ghost (x : V)
    (omega : ConfigSpace (Sym2 (Option V))) :
    abgrCloseGhost omega s(some x, none) = false := by
  simp [abgrCloseGhost, FieldGhostDict.ghostEdges]

@[simp] theorem abgrCloseGhost_physical (a b : V)
    (omega : ConfigSpace (Sym2 (Option V))) :
    abgrCloseGhost omega s(some a, some b) = omega s(some a, some b) := by
  simp [abgrCloseGhost, FieldGhostDict.ghostEdges]

theorem abgrCloseGhost_le (omega : ConfigSpace (Sym2 (Option V))) :
    abgrCloseGhost omega <= omega := by
  intro e
  unfold abgrCloseGhost
  split_ifs <;> simp_all


theorem abgr_exists_keepGhost_walk (omega : ConfigSpace (Sym2 (Option V)))
    {u v : Option V} (p : (openSub (withGhost G) omega).Walk u v) :
    ∀ a : V, u = some a -> v = none ->
      ∃ x : V, omega s(some x, none) = true ∧
        (openSub (withGhost G) (abgrKeepGhost x omega)).Reachable u v := by
  induction p with
  | nil =>
      intro a ha hv
      simp_all
  | @cons u v w huv q ih =>
      intro a ha hw
      subst u
      subst w
      rcases v with _ | b
      · have hopen : omega s(some a, none) = true := by
          simpa [openSub] using huv.2
        refine ⟨a, hopen, ?_⟩
        exact (show (openSub (withGhost G) (abgrKeepGhost a omega)).Adj
          (some a) none from ⟨huv.1, by simpa using hopen⟩).reachable
      · obtain ⟨x, hxopen, hxconn⟩ := ih b rfl rfl
        refine ⟨x, hxopen, ?_⟩
        have hstep :
            (openSub (withGhost G) (abgrKeepGhost x omega)).Adj (some a) (some b) := by
          refine ⟨huv.1, ?_⟩
          simpa using huv.2
        exact hstep.reachable.trans hxconn


theorem abgr_exists_closeGhost_walk (omega : ConfigSpace (Sym2 (Option V)))
    {u v : Option V} (p : (openSub (withGhost G) omega).Walk u v) :
    ∀ a : V, u = some a -> v = none ->
      ∃ x : V, omega s(some x, none) = true ∧
        (openSub (withGhost G) (abgrCloseGhost omega)).Reachable u (some x) := by
  induction p with
  | nil =>
      intro a ha hv
      simp_all
  | @cons u v w huv q ih =>
      intro a ha hw
      subst u
      subst w
      rcases v with _ | b
      · have hopen : omega s(some a, none) = true := by
          simpa [openSub] using huv.2
        exact ⟨a, hopen, Reachable.refl _⟩
      · obtain ⟨x, hxopen, hxconn⟩ := ih b rfl rfl
        refine ⟨x, hxopen, ?_⟩
        have hstep :
            (openSub (withGhost G) (abgrCloseGhost omega)).Adj (some a) (some b) := by
          refine ⟨huv.1, ?_⟩
          simpa using huv.2
        exact hstep.reachable.trans hxconn


theorem abgr_connEvent_iff_exists_keepGhost (o : V)
    (omega : ConfigSpace (Sym2 (Option V))) :
    omega ∈ connEvent (withGhost G) Set.univ (some o) {none} ↔
      ∃ x : V, omega s(some x, none) = true ∧
        abgrKeepGhost x omega ∈ connEvent (withGhost G) Set.univ (some o) {none} := by
  constructor
  · rintro ⟨ho, b, hb, hbg, hconn⟩
    simp only [Set.mem_singleton_iff] at hbg
    subst b
    obtain ⟨p⟩ := hconn
    let q := p.map (SimpleGraph.Embedding.induce Set.univ).toHom
    obtain ⟨x, hxopen, hxconn⟩ :=
      abgr_exists_keepGhost_walk G omega q o rfl rfl
    exact ⟨x, hxopen, ho, none, Set.mem_univ _, Set.mem_singleton _,
      hxconn.elim fun walk => ⟨walk.induce Set.univ (fun _ _ => Set.mem_univ _)⟩⟩
  · rintro ⟨x, hxopen, hxconn⟩
    exact isIncreasing_connEvent (withGhost G) Set.univ (some o) {none}
      (abgrKeepGhost_le x omega) hxconn


theorem abgr_connEvent_iff_exists_physical (o : V)
    (omega : ConfigSpace (Sym2 (Option V))) :
    omega ∈ connEvent (withGhost G) Set.univ (some o) {none} ↔
      ∃ x : V, omega s(some x, none) = true ∧
        abgrCloseGhost omega ∈
          connEvent (withGhost G) Set.univ (some o) {some x} := by
  constructor
  · rintro ⟨ho, b, hb, hbg, hconn⟩
    simp only [Set.mem_singleton_iff] at hbg
    subst b
    obtain ⟨p⟩ := hconn
    let q := p.map (SimpleGraph.Embedding.induce Set.univ).toHom
    obtain ⟨x, hxopen, hxconn⟩ :=
      abgr_exists_closeGhost_walk G omega q o rfl rfl
    exact ⟨x, hxopen, Set.mem_univ _, some x, Set.mem_univ _, Set.mem_singleton _,
      hxconn.elim fun walk => ⟨walk.induce Set.univ (fun _ _ => Set.mem_univ _)⟩⟩
  · rintro ⟨x, hxopen, ho, b, hb, hbx, hconn⟩
    simp only [Set.mem_singleton_iff] at hbx
    subst b
    obtain ⟨p⟩ := hconn
    let q := p.map (SimpleGraph.Embedding.induce Set.univ).toHom
    have hstep : (openSub (withGhost G) omega).Adj (some x) none :=
      ⟨withGhost_adj_some_ghost G x, hxopen⟩
    have hq : (openSub (withGhost G) omega).Reachable (some o) (some x) := by
      exact q.reachable.mono (openSub_mono (withGhost G) (abgrCloseGhost_le omega))
    exact ⟨Set.mem_univ _, none, Set.mem_univ _, Set.mem_singleton _,
      (hq.trans hstep.reachable).elim fun walk =>
        ⟨walk.induce Set.univ (fun _ _ => Set.mem_univ _)⟩⟩


end Sharpness
end StatMech
