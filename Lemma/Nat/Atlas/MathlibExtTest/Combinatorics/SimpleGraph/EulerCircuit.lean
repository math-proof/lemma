import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.MathlibExtTest.Combinatorics.SimpleGraph.EulerCircuit
open MathlibExtTest MathlibExtTest.Combinatorics MathlibExtTest.Combinatorics.SimpleGraph MathlibExtTest.Combinatorics.SimpleGraph.EulerCircuit


namespace MathlibExtTest.Combinatorics.SimpleGraph.EulerCircuit

/--
[zero_mem_triangle_support](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/EulerCircuit.lean)
-/
@[path]
private lemma zero_mem_triangle_support : (0 : Fin 3) ∈ triangle.support := by
  rw [SimpleGraph.mem_support]
  exact ⟨1, SimpleGraph.cycleGraph_adj.mpr (Or.inr rfl)⟩

end MathlibExtTest.Combinatorics.SimpleGraph.EulerCircuit

namespace MathlibExtTest.Combinatorics.SimpleGraph.EulerCircuit

/--
[one_mem_triangle_support](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/EulerCircuit.lean)
-/
@[path]
private lemma one_mem_triangle_support : (1 : Fin 3) ∈ triangle.support := by
  rw [SimpleGraph.mem_support]
  exact ⟨0, SimpleGraph.cycleGraph_adj.mpr (Or.inl rfl)⟩

end MathlibExtTest.Combinatorics.SimpleGraph.EulerCircuit

/--
[connected_hasEulerian_concrete](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/EulerCircuit.lean)
-/
@[path]
lemma connected_hasEulerian_concrete
-- imply
  ∃ (u : Fin 3) (p : triangle.Walk u u), p.IsTrail ∧ p.edges.countP (0 ∈ ·) = 2 := by
-- proof
  obtain ⟨u, p, hp⟩ :=
    (SimpleGraph.cycleGraph_connected (n := 2)).exists_isEulerian (by
      intro v
      rw [SimpleGraph.cycleGraph_degree_three_le]
      exact even_two)
  refine ⟨u, p, hp.isTrail, ?_⟩
  rw [hp.countP_edges_eq_degree, SimpleGraph.cycleGraph_degree_three_le]



-- created on 2026-10-23
