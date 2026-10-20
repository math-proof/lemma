import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.Fleischner
open MetaMathlibExt


/--
[fleischner](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Fleischner.lean)
-/
@[path]
private lemma fleischner_eq
  :
-- imply
  ∀ {V : Type*} [Fintype V] (G H : SimpleGraph V),
    G.IsVertexConnected 2 →
    (∀ u v : V, H.Adj u v ↔ (u ≠ v ∧ (G.Adj u v ∨ ∃ w, G.Adj u w ∧ G.Adj w v))) →
    @SimpleGraph.IsHamiltonian V (fun a b => Classical.propDecidable _) _ H := by
-- proof
  apply MetaMathlibExt.fleischner


-- created on 2026-10-20
