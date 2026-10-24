import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SetFamily.UniformHypergraph
open SetFamily


namespace SetFamily

/--
[isUniform_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SetFamily/UniformHypergraph.lean)
-/
@[path]
lemma isUniform_iff
  {H : Finset (Finset V)}
  {r : ℕ} :
-- imply
  IsUniform H r ↔ ∀ e ∈ H, e.card = r :=
-- proof
  Iff.rfl

end SetFamily

namespace SetFamily

/--
[containsSubgraph_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SetFamily/UniformHypergraph.lean)
-/
@[path]
lemma containsSubgraph_iff
  [DecidableEq V]
  {H : Finset (Finset V)}
  {m k : ℕ} :
-- imply
  ContainsSubgraph H m k ↔
      ∃ S : Finset V, S.card = m ∧ k ≤ (H.filter fun e => e ⊆ S).card :=
-- proof
  Iff.rfl

end SetFamily


-- created on 2026-10-20
-- updated on 2026-10-23
