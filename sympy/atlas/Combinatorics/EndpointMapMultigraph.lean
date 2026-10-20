/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/EndpointMapMultigraph.lean -/

/-
Copyright (c) 2026 Adam Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Kiezun
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Relation

/-!
# Finite edge-identity multigraphs

This file supplies small reusable definitions for finite undirected multigraphs represented by
an edge type and two endpoint maps. Distinct edge values retain parallel-edge identity. Degrees
count endpoint incidences, so a loop contributes two, while `incident` contains a loop only once.
-/

namespace EndpointMapMultigraph

/-- Edges of `F` incident to `v`. An edge appears once even when it is a loop. -/
noncomputable def incident {V E : Type*} (end₁ end₂ : E → V)
    (v : V) (F : Finset E) : Finset E := by
  classical
  exact F.filter (fun e => end₁ e = v ∨ end₂ e = v)

/-- The degree of `v` in `F`, counting each endpoint incidence; a loop contributes two. -/
noncomputable def degreeWithin {V E : Type*} (end₁ end₂ : E → V)
    (F : Finset E) (v : V) : ℕ := by
  classical
  exact (F.filter (fun e => end₁ e = v)).card + (F.filter (fun e => end₂ e = v)).card

/-- The vertices incident with at least one edge of `F`. -/
noncomputable def support {V E : Type*} (end₁ end₂ : E → V)
    (F : Finset E) : Set V := by
  classical
  exact {v | ∃ e ∈ F, end₁ e = v ∨ end₂ e = v}

/-- Undirected adjacency witnessed by an edge of `F`. -/
noncomputable def AdjacentUsing {V E : Type*} (end₁ end₂ : E → V)
    (F : Finset E) (u v : V) : Prop := by
  classical
  exact ∃ e ∈ F, (end₁ e = u ∧ end₂ e = v) ∨ (end₁ e = v ∧ end₂ e = u)

/-- The edge set `F` is connected on its support. -/
noncomputable def IsConnectedOnSupport {V E : Type*} (end₁ end₂ : E → V)
    (F : Finset E) : Prop :=
  ∀ u ∈ support end₁ end₂ F, ∀ v ∈ support end₁ end₂ F,
    Relation.ReflTransGen (AdjacentUsing end₁ end₂ F) u v

/-- A circuit is a nonempty connected 2-regular edge set. This includes a loop as a
1-circuit and two parallel edges between distinct vertices as a 2-circuit. -/
noncomputable def IsCircuit {V E : Type*} (end₁ end₂ : E → V)
    (F : Finset E) : Prop :=
  F.Nonempty ∧ IsConnectedOnSupport end₁ end₂ F ∧
    ∀ v ∈ support end₁ end₂ F, degreeWithin end₁ end₂ F v = 2

/-- The cut of `X`: edges with exactly one endpoint in `X`. Loops never cross a cut. -/
noncomputable def cut {V E : Type*} [Fintype E] (end₁ end₂ : E → V)
    (X : Finset V) : Finset E := by
  classical
  exact Finset.univ.filter (fun e => decide (end₁ e ∈ X) != decide (end₂ e ∈ X))

@[simp] theorem mem_incident {V E : Type*} (end₁ end₂ : E → V) (v : V)
    (F : Finset E) (e : E) :
    e ∈ incident end₁ end₂ v F ↔ e ∈ F ∧ (end₁ e = v ∨ end₂ e = v) := by
  classical
  simp [incident]

theorem incident_swap {V E : Type*} (end₁ end₂ : E → V) (v : V) (F : Finset E) :
    incident end₂ end₁ v F = incident end₁ end₂ v F := by
  classical
  ext e
  simp [or_comm]

theorem degreeWithin_swap {V E : Type*} (end₁ end₂ : E → V) (F : Finset E) (v : V) :
    degreeWithin end₂ end₁ F v = degreeWithin end₁ end₂ F v := by
  classical
  simp [degreeWithin, Nat.add_comm]

@[simp] theorem mem_support {V E : Type*} (end₁ end₂ : E → V) (F : Finset E) (v : V) :
    v ∈ support end₁ end₂ F ↔ ∃ e ∈ F, end₁ e = v ∨ end₂ e = v := by
  classical
  simp [support]

theorem support_swap {V E : Type*} (end₁ end₂ : E → V) (F : Finset E) :
    support end₂ end₁ F = support end₁ end₂ F := by
  ext v
  simp [or_comm]

theorem adjacentUsing_symm {V E : Type*} (end₁ end₂ : E → V) (F : Finset E)
    {u v : V} : AdjacentUsing end₁ end₂ F u v ↔ AdjacentUsing end₁ end₂ F v u := by
  classical
  simp [AdjacentUsing, and_comm, or_comm]

theorem adjacentUsing_swap {V E : Type*} (end₁ end₂ : E → V) (F : Finset E)
    (u v : V) : AdjacentUsing end₂ end₁ F u v ↔ AdjacentUsing end₁ end₂ F u v := by
  classical
  simp [AdjacentUsing, and_comm, or_comm]

theorem isConnectedOnSupport_swap {V E : Type*} (end₁ end₂ : E → V) (F : Finset E) :
    IsConnectedOnSupport end₂ end₁ F ↔ IsConnectedOnSupport end₁ end₂ F := by
  have hadj : AdjacentUsing end₂ end₁ F = AdjacentUsing end₁ end₂ F := by
    funext u v
    exact propext (adjacentUsing_swap end₁ end₂ F u v)
  rw [IsConnectedOnSupport, IsConnectedOnSupport, support_swap, hadj]

theorem isCircuit_swap {V E : Type*} (end₁ end₂ : E → V) (F : Finset E) :
    IsCircuit end₂ end₁ F ↔ IsCircuit end₁ end₂ F := by
  simp only [IsCircuit, support_swap, degreeWithin_swap, isConnectedOnSupport_swap]

/-- In a loopless edge set, endpoint-incidence degree equals the number of
distinct incident edges. -/
theorem degreeWithin_eq_card_incident_of_loopless {V E : Type*} (end₁ end₂ : E → V)
    (F : Finset E) (v : V) (h : ∀ e ∈ F, end₁ e ≠ end₂ e) :
    degreeWithin end₁ end₂ F v = (incident end₁ end₂ v F).card := by
  classical
  let F₁ := F.filter (fun e => end₁ e = v)
  let F₂ := F.filter (fun e => end₂ e = v)
  have hdisjoint : Disjoint F₁ F₂ := by
    rw [Finset.disjoint_left]
    intro e he₁ he₂
    simp only [F₁, F₂, Finset.mem_filter] at he₁ he₂
    exact h e he₁.1 (he₁.2.trans he₂.2.symm)
  have hunion : F₁ ∪ F₂ = incident end₁ end₂ v F := by
    ext e
    simp only [F₁, F₂, incident, Finset.mem_union, Finset.mem_filter]
    tauto
  rw [degreeWithin]
  change F₁.card + F₂.card = _
  rw [← Finset.card_union_of_disjoint hdisjoint, hunion]

@[simp] theorem mem_cut {V E : Type*} [Fintype E] (end₁ end₂ : E → V)
    (X : Finset V) (e : E) :
    e ∈ cut end₁ end₂ X ↔ (end₁ e ∈ X) ≠ (end₂ e ∈ X) := by
  classical
  simp [cut]

theorem cut_swap {V E : Type*} [Fintype E] (end₁ end₂ : E → V) (X : Finset V) :
    cut end₂ end₁ X = cut end₁ end₂ X := by
  ext e
  simp only [mem_cut]
  exact ne_comm

theorem degreeWithin_singleton_loop {V E : Type*} (end₁ end₂ : E → V) (e : E)
    (h : end₁ e = end₂ e) : degreeWithin end₁ end₂ {e} (end₁ e) = 2 := by
  classical
  rw [degreeWithin, Finset.filter_singleton, Finset.filter_singleton]
  simp [h.symm]

theorem loop_not_mem_cut {V E : Type*} [Fintype E] (end₁ end₂ : E → V)
    (X : Finset V) (e : E) (h : end₁ e = end₂ e) : e ∉ cut end₁ end₂ X := by
  classical
  simp [h]

@[simp] theorem isConnectedOnSupport_empty {V E : Type*} (end₁ end₂ : E → V) :
    IsConnectedOnSupport end₁ end₂ (∅ : Finset E) := by
  simp [IsConnectedOnSupport]

@[simp] theorem not_isCircuit_empty {V E : Type*} (end₁ end₂ : E → V) :
    ¬IsCircuit end₁ end₂ (∅ : Finset E) := by
  simp [IsCircuit]

end EndpointMapMultigraph
