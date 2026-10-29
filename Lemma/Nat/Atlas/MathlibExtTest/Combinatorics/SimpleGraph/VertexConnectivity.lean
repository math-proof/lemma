import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.MathlibExtTest.Combinatorics.SimpleGraph.VertexConnectivity
open MathlibExtTest MathlibExtTest.Combinatorics MathlibExtTest.Combinatorics.SimpleGraph MathlibExtTest.Combinatorics.SimpleGraph.VertexConnectivity


namespace MathlibExtTest.Combinatorics.SimpleGraph.VertexConnectivity

/--
[completeGraph_isVertexConnected_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/VertexConnectivity.lean)
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

end MathlibExtTest.Combinatorics.SimpleGraph.VertexConnectivity

namespace MathlibExtTest.Combinatorics.SimpleGraph.VertexConnectivity

/--
[complete_four_has_cycle_through](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/VertexConnectivity.lean)
-/
@[path]
lemma complete_four_has_cycle_through :
-- imply
  ∃ c : (⊤ : SimpleGraph (Fin 4)).Walk 0 0, c.IsCycle ∧ 3 ≤ c.length := by
-- proof
  obtain ⟨c, hc⟩ := completeGraph_isVertexConnected_two.exists_cycle_through 0
  exact ⟨c, hc, hc.three_le_length⟩

end MathlibExtTest.Combinatorics.SimpleGraph.VertexConnectivity


-- created on 2026-10-23
-- updated on 2026-10-28
