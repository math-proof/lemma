import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.FallingBinomialTransform
open MetaMathlibExt


/--
[falling_equiv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FallingBinomialTransform.lean)
-/
@[path]
private lemma falling_equiv_eq
  {a : ℕ → ℤ}
  {k : ℤ} :
-- imply
  (if 0 ≤ k then multipleBinomialTransform k.toNat a
    else Nat.iterate (fallingKBinomialTransform (-1)) (-k).toNat a) =
    fallingKBinomialTransform k a := by
-- proof
  apply MetaMathlibExt.falling_equiv a k


-- created on 2026-10-20
