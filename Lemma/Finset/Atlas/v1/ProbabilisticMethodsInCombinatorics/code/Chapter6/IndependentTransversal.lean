import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter6.IndependentTransversal
open SimpleGraph Finset IndependentTransversal


namespace IndependentTransversal

/--
[IsIndependentTransversal.of_subset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter6/IndependentTransversal.lean)
-/
@[path]
lemma IsIndependentTransversal.of_subset
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {r : ℕ}
  {parts parts' : Fin r → Finset V}
  {f : Fin r → V}
-- given
  (h_sub : ∀ i, parts' i ⊆ parts i)
  (hf : IsIndependentTransversal G parts' f) :
-- imply
  IsIndependentTransversal G parts f :=
-- proof
  ⟨fun i => h_sub i (hf.1 i), hf.2⟩
/-- LLL-based existence of an independent transversal in the *equal-part* case: if every part
has the same size $k$ and $2 e \Delta(G) \le k$, then there is an independent transversal,
obtained by sampling each $f(i)$ uniformly from `parts i` and applying the LLL. -/

end IndependentTransversal


-- created on 2026-10-23
