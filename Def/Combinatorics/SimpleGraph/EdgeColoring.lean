/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeColoring.lean -/

module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Combinatorics.Hall.Basic

@[expose] public section

section

namespace MathlibExt.Combinatorics.SimpleGraph.EdgeColoringWanted

/-!
# Edge coloring landmarks

Records Vizing and König edge-coloring theorems.
-/

/-- A proper edge coloring: distinct edges incident at a common vertex
receive different colors. -/
def IsProperEdgeColoring {V K : Type*} {G : _root_.SimpleGraph V}
    (C : G.EdgeLabeling K) : Prop :=
  ∀ {v w₁ w₂ : V} (h₁ : G.Adj v w₁) (h₂ : G.Adj v w₂), w₁ ≠ w₂ →
    C ⟨Sym2.mk v w₁, G.mem_edgeSet.mpr h₁⟩ ≠ C ⟨Sym2.mk v w₂, G.mem_edgeSet.mpr h₂⟩

end MathlibExt.Combinatorics.SimpleGraph.EdgeColoringWanted
end
