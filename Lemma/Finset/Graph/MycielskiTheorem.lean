import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Graph.MycielskiTheorem
open scoped SimpleGraph
open MetaMathlibExt


/--
[mycielski_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/MycielskiTheorem.lean)
-/
@[path]
private lemma mycielski_theorem_eq
  :
-- imply
  (∀ (V : Type*) [Fintype V] (G : SimpleGraph V),
    ∃ (W : Type*) (_ : Fintype W) (H : SimpleGraph W),
    G ⊑ H ∧
    Fintype.card V < Fintype.card W ∧
    (G.CliqueFree 3 → H.CliqueFree 3) ∧
    (G.chromaticNumber ≠ ⊤ → H.chromaticNumber = G.chromaticNumber + 1)) ∧
    ∀ (k : ℕ), ∃ (W : Type*) (_ : Fintype W) (H : SimpleGraph W),
    H.CliqueFree 3 ∧ (↑k ≤ H.chromaticNumber) := by
-- proof
  apply MetaMathlibExt.mycielski_theorem


-- created on 2026-10-20
