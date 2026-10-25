/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/EulerCircuit.lean -/


import Lemma.SimpleGraph.EulerCircuit
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Abbrev.MathlibExtTest.Combinatorics.SimpleGraph.EulerCircuit


namespace MathlibExtTest.Combinatorics.SimpleGraph.EulerCircuit

example : (triangle.induce triangle.support).Reachable
    ⟨0, zero_mem_triangle_support⟩ ⟨1, one_mem_triangle_support⟩ := by
  have hreach : triangle.Reachable 0 1 :=
    SimpleGraph.cycleGraph_connected (n := 2) 0 1
  exact hreach.induce_support zero_mem_triangle_support one_mem_triangle_support

example : ∃ (u : Fin 3) (p : triangle.Walk u u),
    p.IsTrail ∧ ∀ e ∈ triangle.edgeSet, e ∈ p.edges := by
  have htriangle : triangle.Connected := SimpleGraph.cycleGraph_connected (n := 2)
  have hs : triangle.support = Set.univ := htriangle.preconnected.support_eq_univ
  have hsupport : (triangle.induce triangle.support).Connected := by
    rw [hs]
    exact triangle.induceUnivIso.connected_iff.mpr htriangle
  obtain ⟨u, p, hp⟩ := SimpleGraph.ConnectedSupport.exists_isEulerian hsupport (by
    intro v
    rw [SimpleGraph.cycleGraph_degree_three_le]
    exact even_two)
  exact ⟨u, p, hp.isTrail, fun e he ↦ hp.mem_edges_iff.mpr he⟩

end MathlibExtTest.Combinatorics.SimpleGraph.EulerCircuit
