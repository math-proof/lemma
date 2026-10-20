/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/VertexTransitive.lean -/

/-
Copyright (c) 2026 Adam Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Kiezun
-/

import Mathlib.Combinatorics.SimpleGraph.Maps

namespace SimpleGraph

/-- A graph is vertex-transitive when its automorphism group acts transitively
on vertices. -/
def IsVertexTransitive {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ u v : V, ∃ e : G ≃g G, e u = v

@[simp] theorem isVertexTransitive_of_subsingleton {V : Type*} [Subsingleton V]
    (G : SimpleGraph V) : G.IsVertexTransitive := by
  intro u v
  exact ⟨SimpleGraph.Iso.refl, Subsingleton.elim _ _⟩

end SimpleGraph
