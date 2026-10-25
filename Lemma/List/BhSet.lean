import Mathlib
import sympy.Basic
import Def.Combinatorics.Additive.BhSet.Part2


/--
[BhSet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Additive/BhSet.lean)
-/
@[path]
private lemma sum_ne_proof_irrel_eq
-- given
  {G : Type*} [Add G]
  (l : List G)
  (e₁ e₂ : l ≠ []) :
-- imply
  AdditiveCombinatorics.sumNE l e₁ = AdditiveCombinatorics.sumNE l e₂ := by
-- proof
  apply AdditiveCombinatorics.sumNE_proof_irrel


-- created on 2026-10-11
