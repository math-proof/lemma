import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.GaussianQBinomial
open Finset
open MetaMathlibExt


/--
[gaussian_pair_sorted_expansion](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/GaussianQBinomial.lean)
-/
@[path]
private lemma gaussian_pair_sorted_expansion_eq
  {n k : ℕ} :
-- imply
  let words : Finset (Fin n → Fin 2) := by
-- proof
  apply MetaMathlibExt.gaussian_pair_sorted_expansion n k


-- created on 2026-10-20
