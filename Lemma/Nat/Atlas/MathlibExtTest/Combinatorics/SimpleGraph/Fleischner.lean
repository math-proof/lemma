import Mathlib
import Initialize.Tactic.Attr.Basic


namespace MathlibExtTest.Combinatorics.SimpleGraph.Fleischner

/--
[completeGraph_isVertexConnected_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/Fleischner.lean)
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

end MathlibExtTest.Combinatorics.SimpleGraph.Fleischner

namespace MathlibExtTest.Combinatorics.SimpleGraph.Fleischner

/--
[fleischner_complete_three](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/Fleischner.lean)
-/
@[path]
lemma fleischner_complete_three :
-- imply
  ∃ (x : Fin 3) (p : (⊤ : SimpleGraph (Fin 3)).Walk x x), @SimpleGraph.Walk.IsHamiltonianCycle (Fin 3) (fun a b ↦ Classical.propDecidable (a = b)) _ x p ∧ p.length = 3 := by
-- proof
  classical
  have hhamiltonian := MetaMathlibExt.fleischner
    (⊤ : SimpleGraph (Fin 3)) (⊤ : SimpleGraph (Fin 3))
    completeGraph_isVertexConnected_two (by
      intro u v
      simp only [SimpleGraph.top_adj]
      constructor
      · intro huv
        exact ⟨huv, Or.inl huv⟩
      · exact fun h ↦ h.1)
  obtain ⟨x, p, hp⟩ := hhamiltonian (by decide)
  have hlength :=
    ((@SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_length_eq
      (Fin 3) (fun a b ↦ Classical.propDecidable (a = b))
      (⊤ : SimpleGraph (Fin 3)) x p inferInstance).mp hp).2
  exact ⟨x, p, hp, by simpa using hlength⟩

end MathlibExtTest.Combinatorics.SimpleGraph.Fleischner


-- created on 2026-10-23
-- updated on 2026-10-28
