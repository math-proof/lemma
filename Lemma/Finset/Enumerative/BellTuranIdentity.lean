import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.BellTuranIdentity
open MetaMathlibExt


/--
[bell_turan_identity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BellTuranIdentity.lean)
-/
@[path]
private lemma bell_turan_identity_eq
  {n : ℕ}
-- given
  (hn : 2 ≤ n) :
-- imply
  (Nat.bell (n - 1) : ℝ) * (Nat.bell (n + 1) : ℝ) -
    (Nat.bell n : ℝ) ^ 2 =
    (1 / (2 * Real.exp 1 ^ 2)) *
    ∑' k : {k : ℕ // 2 ≤ k},
    ∑ j ∈ Finset.Icc 1 (k.1 - 1),
    (((j : ℝ) ^ (n - 1) * ((k.1 - j : ℕ) : ℝ) ^ (n - 1)) /
    ((Nat.factorial j : ℝ) * (Nat.factorial (k.1 - j) : ℝ))) *
    ((k.1 : ℝ) - 2 * (j : ℝ)) ^ 2 := by
-- proof
  apply MetaMathlibExt.bell_turan_identity n hn


-- created on 2026-10-20
