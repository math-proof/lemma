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
end EndpointMapMultigraph
