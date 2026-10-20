import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.DominoTilingSequenceFactorization
open MetaMathlibExt


/--
[on](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/DominoTilingSequenceFactorization.lean)
-/
@[path]
private lemma on_eq
  {n-1} :
-- imply
  ∀ (d g : Nat → Nat), d 1 = 1 → d 2 = 8 → d 3 = 95 → d 4 = 1183 →
    (∀ n, 1 ≤ n → d (n + 4) + 32 * d (n + 2) + d n = 15 * d (n + 3) + 15 * d (n + 1)) →
    g 1 = 1 → g 2 = 4 →
    (∀ n, 1 ≤ n → g (n + 2) + g n = 5 * g (n + 1)) →
    ∀ n, 1 ≤ n → d n = g n * Nat.fib (2 * n - 1) := by
-- proof
  apply MetaMathlibExt.on

/--
[domino_tiling_sequence_factorization](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/DominoTilingSequenceFactorization.lean)
-/
@[path]
private lemma domino_tiling_sequence_factorization_eq
  :
-- imply
  ∀ (d g : Nat → Nat), d 1 = 1 → d 2 = 8 → d 3 = 95 → d 4 = 1183 →
    (∀ n, 1 ≤ n → d (n + 4) + 32 * d (n + 2) + d n = 15 * d (n + 3) + 15 * d (n + 1)) →
    g 1 = 1 → g 2 = 4 →
    (∀ n, 1 ≤ n → g (n + 2) + g n = 5 * g (n + 1)) →
    ∀ n, 1 ≤ n → d n = g n * Nat.fib (2 * n - 1) := by
-- proof
  apply MetaMathlibExt.domino_tiling_sequence_factorization


-- created on 2026-10-20
