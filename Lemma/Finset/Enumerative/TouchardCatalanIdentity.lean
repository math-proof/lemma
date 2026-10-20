import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.TouchardCatalanIdentity
open MetaMathlibExt


/--
[touchard_catalan_identity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/TouchardCatalanIdentity.lean)
-/
@[path]
private lemma touchard_catalan_identity_eq
  {n : Nat} :
-- imply
  catalan (n + 1) =
    (Finset.range (n / 2 + 1)).sum
    (fun i => catalan i * 2 ^ (n - 2 * i) * Nat.choose n (2 * i)) := by
-- proof
  apply MetaMathlibExt.touchard_catalan_identity n


-- created on 2026-10-20
