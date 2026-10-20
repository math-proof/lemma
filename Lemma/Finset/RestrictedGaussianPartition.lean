import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.RestrictedGaussianPartition
open MetaMathlibExt


/--
[basic_ancestor_is_restricted](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RestrictedGaussianPartition.lean)
-/
@[path]
private lemma basic_ancestor_is_restricted_eq
  {q n : Nat}
  {blocks : List Block}
  {G : GaussianPartition}
-- given
  (hq : IsPrimePow q)
  (hn : 0 < n)
  (hvalid : BlocksStructValid blocks n)
  (hsorted : (basicGlobalDims q blocks).Pairwise (fun a b : Nat => a ≥ b))
  (hdims : G.dims = basicGlobalDims q blocks) :
-- imply
  IsRestrictedGaussianPartition q n G := by
-- proof
  apply MetaMathlibExt.basic_ancestor_is_restricted q n blocks G hq hn hvalid hsorted hdims


-- created on 2026-10-20
