import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.MinimalPermutationsEnumeration
open MetaMathlibExt


/--
[minimal_permutations_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MinimalPermutationsEnumeration.lean)
-/
@[path]
private lemma minimal_permutations_card_eq
  {d : ℕ} :
-- imply
  (Finset.univ.filter fun σ : Equiv.Perm (Fin (d + 2)) =>
    (Finset.univ.filter fun i : Fin (d + 1) =>
    σ i.castSucc > σ i.succ).card = d ∧
    ∀ j : Fin (d + 2),
    (Finset.univ.filter fun i : Fin d =>
    σ (j.succAbove i.castSucc) > σ (j.succAbove i.succ)).card < d).card =
    2 ^ (d + 2) - (d + 1) * (d + 2) - 2 := by
-- proof
  apply MetaMathlibExt.minimal_permutations_card d


-- created on 2026-10-20
