import Mathlib
import sympy.Basic
import sympy.atlas.MathlibExtTest.Combinatorics.SimpleGraph.Riha
open MathlibExtTest MathlibExtTest.Combinatorics MathlibExtTest.Combinatorics.SimpleGraph MathlibExtTest.Combinatorics.SimpleGraph.Riha


namespace MathlibExtTest.Combinatorics.SimpleGraph.Riha

/--
[completeGraph_isVertexConnected_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/Riha.lean)
-/
@[path]
private lemma completeGraph_isVertexConnected_two :
  SimpleGraph.IsVertexConnected 2 (⊤ : SimpleGraph (Fin 4)) := by
  rw [SimpleGraph.isVertexConnected_two_iff]
  refine ⟨by decide, SimpleGraph.connected_top, ?_⟩
  intro v
  rw [SimpleGraph.induce_top]
  let _ : Nonempty {x : Fin 4 // x ∈ (↑({v} : Finset (Fin 4)) : Set (Fin 4))ᶜ} :=
    Fintype.card_pos_iff.mp (by
      rw [Fintype.card_compl_set]
      simp)
  exact SimpleGraph.connected_top

end MathlibExtTest.Combinatorics.SimpleGraph.Riha

namespace MathlibExtTest.Combinatorics.SimpleGraph.Riha

/--
[riha_complete_four](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/Riha.lean)
-/
@[path]
lemma riha_complete_four
-- imply
  ∃ (c : (⊤ : SimpleGraph (Fin 4)).Walk 0 0) (y : Fin 4), c.IsCycle ∧ y ≠ 0 ∧ y ∈ c.support ∧ ((⊤ : SimpleGraph (Fin 4)).Adj y 3 → 3 ∈ c.support) := by
-- proof
  obtain ⟨c, hc, y, hy, hbound⟩ :=
    completeGraph_isVertexConnected_two.exists_cycle_bound_vertex 0
  exact ⟨c, y, hc, hy, hbound.1, fun hy3 ↦ hbound.2 hy3⟩

end MathlibExtTest.Combinatorics.SimpleGraph.Riha


-- created on 2026-10-23
