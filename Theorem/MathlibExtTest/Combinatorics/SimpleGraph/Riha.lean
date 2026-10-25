/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/Riha.lean -/


import Def.Combinatorics.SimpleGraph.Riha
import Lemma.SimpleGraph.Riha


namespace MathlibExtTest.Combinatorics.SimpleGraph.Riha

example :
    ∃ (c : (⊤ : SimpleGraph (Fin 4)).Walk 0 0) (y : Fin 4),
      y ≠ 0 ∧ ∀ ⦃z⦄, (⊤ : SimpleGraph (Fin 4)).Adj y z → z ∈ c.support := by
  obtain ⟨c, -, y, hy, hbound⟩ :=
    completeGraph_isVertexConnected_two.exists_cycle_bound_vertex 0
  have hbound' := (SimpleGraph.Walk.isBoundVertex_iff c y).mp hbound
  exact ⟨c, y, hy, hbound'.2⟩

end MathlibExtTest.Combinatorics.SimpleGraph.Riha
