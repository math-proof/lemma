import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.ErdosGallai
open MathlibExt.Combinatorics.SimpleGraph.ErdosGallaiWanted


/--
[erdos_gallai](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/ErdosGallai.lean)
-/
@[path]
private lemma erdos_gallai_eq
  [Fintype V] [DecidableEq V]
  {d : V → ℕ} :
-- imply
  (∃ G : SimpleGraph V, ∃ _ : DecidableRel G.Adj, ∀ v, G.degree v = d v) ↔
    Even (∑ v : V, d v) ∧
    ∀ S : Finset V,
    ∑ v ∈ S, d v ≤ S.card * (S.card - 1) +
    ∑ v ∈ Finset.univ \ S, min (d v) S.card := by
-- proof
  apply MathlibExt.Combinatorics.SimpleGraph.ErdosGallaiWanted.erdos_gallai d


-- created on 2026-10-20
