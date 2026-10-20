import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SetFamily.UniformHypergraph
open SetFamily


/--
[isUniform_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SetFamily/UniformHypergraph.lean)
-/
@[path]
private lemma isUniform_iff_eq
  {H : Finset (Finset V)}
  {r : ℕ} :
-- imply
  IsUniform H r ↔ ∀ e ∈ H, e.card = r := by
-- proof
  apply SetFamily.isUniform_iff H r

/--
[containsSubgraph_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SetFamily/UniformHypergraph.lean)
-/
@[path]
private lemma containsSubgraph_iff_eq
  [DecidableEq V]
  {H : Finset (Finset V)}
  {m k : ℕ} :
-- imply
  ContainsSubgraph H m k ↔
      ∃ S : Finset V, S.card = m ∧ k ≤ (H.filter fun e => e ⊆ S).card := by
-- proof
  apply SetFamily.containsSubgraph_iff H m k


-- created on 2026-10-20
