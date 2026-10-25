/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/EndpointMapMultigraph.lean -/

/-
Copyright (c) 2026 Adam Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Kiezun
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Relation
import Def.Combinatorics.EndpointMapMultigraph
/-!
# Finite edge-identity multigraphs

This file supplies small reusable definitions for finite undirected multigraphs represented by
an edge type and two endpoint maps. Distinct edge values retain parallel-edge identity. Degrees
count endpoint incidences, so a loop contributes two, while `incident` contains a loop only once.
-/


namespace EndpointMapMultigraph

@[simp] theorem mem_incident {V E : Type*} (end₁ end₂ : E → V) (v : V)
    (F : Finset E) (e : E) :
    e ∈ incident end₁ end₂ v F ↔ e ∈ F ∧ (end₁ e = v ∨ end₂ e = v) := by
  classical
  simp [incident]

end EndpointMapMultigraph
