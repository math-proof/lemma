import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Combinatorics.SimpleGraph.FleischnerStrong.Part23
import Lemma.SimpleGraph.FleischnerStrong
open MathlibExtTest MathlibExtTest.Combinatorics MathlibExtTest.Combinatorics.SimpleGraph


namespace MathlibExtTest.Combinatorics.SimpleGraph.FleischnerStrong

/--
[completeGraph_isVertexConnected_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
private lemma completeGraph_isVertexConnected_two :
  SimpleGraph.IsVertexConnected 2 (⊤ : SimpleGraph (Fin 3)) := by
  rw [SimpleGraph.isVertexConnected_two_iff]
  refine ⟨by decide, SimpleGraph.connected_top, ?_⟩
  intro v
  rw [SimpleGraph.induce_top]
  let _ : Nonempty {x : Fin 3 // x ∈ (↑({v} : Finset (Fin 3)) : Set (Fin 3))ᶜ} :=
    Fintype.card_pos_iff.mp (by
      rw [Fintype.card_compl_set]
      simp)
  exact SimpleGraph.connected_top

end MathlibExtTest.Combinatorics.SimpleGraph.FleischnerStrong

namespace MathlibExtTest.Combinatorics.SimpleGraph.FleischnerStrong

/--
[complete_three_hasStrongSquareCycle](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/FleischnerStrong.lean)
-/
@[path]
lemma complete_three_hasStrongSquareCycle
-- imply
  ∃ p : (⊤ : SimpleGraph (Fin 3)).square.Walk 0 0, p.IsHamiltonianCycle ∧ p.length = 3 ∧ (⊤ : SimpleGraph (Fin 3)).Adj 0 p.snd ∧ (⊤ : SimpleGraph (Fin 3)).Adj p.penultimate 0 := by
-- proof
  obtain ⟨p, hp, hfirst, hlast⟩ :=
    completeGraph_isVertexConnected_two.hasStrongSquareCycle 0
  have hlength :=
    (SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_length_eq.mp hp).2
  exact ⟨p, hp, by simpa using hlength, hfirst, hlast⟩

end MathlibExtTest.Combinatorics.SimpleGraph.FleischnerStrong


-- created on 2026-10-23
