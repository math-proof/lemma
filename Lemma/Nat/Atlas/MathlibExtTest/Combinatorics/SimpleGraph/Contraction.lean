import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.MathlibExtTest.Combinatorics.SimpleGraph.Contraction
open MathlibExtTest MathlibExtTest.Combinatorics MathlibExtTest.Combinatorics.SimpleGraph MathlibExtTest.Combinatorics.SimpleGraph.Contraction


namespace MathlibExtTest.Combinatorics.SimpleGraph.Contraction

/--
[completeGraph_isVertexConnected_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/Contraction.lean)
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

end MathlibExtTest.Combinatorics.SimpleGraph.Contraction

namespace MathlibExtTest.Combinatorics.SimpleGraph.Contraction

/--
[collapseOutside_concrete](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/Contraction.lean)
-/
@[path]
lemma collapseOutside_concrete :
-- imply
  SimpleGraph.collapseOutside retained 0 = some zero ∧ SimpleGraph.collapseOutside retained 2 = none := by
-- proof
  constructor
  · exact SimpleGraph.collapseOutside_of_mem retained (by simp [retained])
  · exact SimpleGraph.collapseOutside_of_notMem retained (by simp [retained])

end MathlibExtTest.Combinatorics.SimpleGraph.Contraction


-- created on 2026-10-23
-- updated on 2026-10-28
