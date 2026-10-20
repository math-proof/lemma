import Mathlib
import sympy.Basic
import sympy.atlas.InformationTheory.KraftMcMillan
open scoped BigOperators
open MathlibExt.InformationTheory.KraftMcMillan


/--
[kraft_mcmillan_lengths](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/KraftMcMillan.lean)
-/
@[path]
private lemma kraft_mcmillan_lengths_eq
  [Fintype α] [Fintype β]
  {l : α → ℕ}
-- given
  (hq : 2 ≤ Fintype.card β) :
-- imply
  (∃ code : α → List β, IsPrefixFree code ∧ ∀ a, (code a).length = l a)
    ↔ ∑ a : α, (1 : ℝ) / (Fintype.card β : ℝ) ^ (l a) ≤ 1 := by
-- proof
  apply MathlibExt.InformationTheory.KraftMcMillan.kraft_mcmillan_lengths l hq


-- created on 2026-10-20
