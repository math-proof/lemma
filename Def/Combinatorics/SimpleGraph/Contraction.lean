/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Contraction.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

module

public import Theorem.Combinatorics.SimpleGraph.VertexConnectivity
public import Theorem.SimpleGraph.VertexConnectivity

@[expose] public section

/-!
# Contracting the complement of a vertex set

This file contracts every vertex outside a set to one new vertex. The construction is used by
the induction in Fleischner's theorem.
-/


namespace SimpleGraph

/-- Send vertices in `D` to their subtype copy and every other vertex to `none`. -/
noncomputable def collapseOutside {V : Type*} (D : Set V) : V → Option D := by
  classical
  exact fun v ↦ if hv : v ∈ D then some ⟨v, hv⟩ else none

end SimpleGraph
