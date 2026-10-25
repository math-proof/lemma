import Mathlib
import sympy.Basic
import Theorem.Combinatorics.SimpleGraph.VertexConnectivity
import Lemma.SimpleGraph.VertexConnectivity
import Lemma.SimpleGraph.FleischnerStrong
import Lemma.SimpleGraph.Square
import Theorem.Combinatorics.SimpleGraph.FleischnerStrong.Part23
import Theorem.Combinatorics.SimpleGraph.Square


namespace MetaMathlibExt

/--
[fleischner](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Fleischner.lean)
-/
@[path]
lemma fleischner
  :
-- imply
  ∀ {V : Type*} [Fintype V] (G H : SimpleGraph V),
    G.IsVertexConnected 2 →
    (∀ u v : V, H.Adj u v ↔ (u ≠ v ∧ (G.Adj u v ∨ ∃ w, G.Adj u w ∧ G.Adj w v))) →
    @SimpleGraph.IsHamiltonian V (fun a b => Classical.propDecidable _) _ H := by
-- proof
  intro V _ G H hG hH
  rw [SimpleGraph.eq_square_iff.mpr hH]
  classical
  intro _
  have hV : Nonempty V := Fintype.card_pos_iff.mp (by
    have := hG.card_gt
    omega)
  let x : V := Classical.choice hV
  obtain ⟨p, hp, _, _⟩ := hG.hasStrongSquareCycle x
  exact ⟨x, p, hp⟩

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
