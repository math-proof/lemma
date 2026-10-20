import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.BrentOsbornBinomialAbsoluteMoment
open MetaMathlibExt


/--
[brent_osborn_binomial_absolute_moment](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BrentOsbornBinomialAbsoluteMoment.lean)
-/
@[path]
private lemma brent_osborn_binomial_absolute_moment_eq
  {n : ℕ} :
-- imply
  (∑ k : Fin (2 * n + 1), ∑ l : Fin (2 * n + 1),
    Nat.choose (2 * n) k.1 * Nat.choose (2 * n) l.1 *
    Int.natAbs (((k.1 : ℤ) - n) ^ 2 - ((l.1 : ℤ) - n) ^ 2)) =
    2 * n ^ 2 * (Nat.choose (2 * n) n) ^ 2 := by
-- proof
  apply MetaMathlibExt.brent_osborn_binomial_absolute_moment n


-- created on 2026-10-20
