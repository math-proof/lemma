/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/CycleCover.lean -/


import sympy.atlas.Combinatorics.SimpleGraph.CycleCover

namespace SimpleGraph

variable {V : Type*}

/-- The empty multiset of cycles has total length zero. -/
example (G : SimpleGraph V) : totalLength (∅ : Multiset (Cycle G)) = 0 := by
  simp [totalLength]

/-- Cycle length and edges project the underlying walk. -/
example {G : SimpleGraph V} (c : Cycle G) : c.length = c.walk.length := rfl
example {G : SimpleGraph V} (c : Cycle G) : c.edges = c.walk.edges := rfl

/-- `Cycle` is usable over a type with no `Fintype` or `DecidableEq` instance. -/
example {W : Type*} {G : SimpleGraph W} (c : Cycle G) : c.length = c.walk.length := rfl

/-- The empty family covers an edgeless graph. -/
example : (⊥ : SimpleGraph (Fin 2)).IsCycleCover ∅ := by
  simp [IsCycleCover]

/-- The empty family does not cover the complete graph on two vertices. -/
example : ¬ (⊤ : SimpleGraph (Fin 2)).IsCycleCover ∅ := by
  intro h
  have hedge : s((0 : Fin 2), 1) ∈ (⊤ : SimpleGraph (Fin 2)).edgeFinset := by simp
  obtain ⟨c, hc, _⟩ := h _ hedge
  simp at hc

end SimpleGraph
