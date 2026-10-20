/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/SturmianWord.lean -/

import Mathlib.Data.Int.Basic

namespace MetaMathlibExt

/-- Count of `1`s in the length-`n` factor of `x` starting at `i`
    (concept `jis_term_4c219044135404e2d10fb16f`, statement `jis_a07921e69f2b6f8112afb1b1`). -/
def factorOnes (x : ℕ → Bool) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | i, n + 1 => factorOnes x i n + if x (i + n) then 1 else 0

/-- A binary word is balanced when any two factors of the same length
    have `1`-counts whose absolute difference is at most `1`
    (concept `jis_term_4c219044135404e2d10fb16f`, statement `jis_a07921e69f2b6f8112afb1b1`). -/
def IsBalanced (x : ℕ → Bool) : Prop :=
  ∀ i j n : ℕ, (((factorOnes x i n : ℤ) - (factorOnes x j n : ℤ)).natAbs ≤ 1)

/-- A one-sided word is aperiodic when it is not ultimately periodic:
    no positive period `p` and preperiod `N` satisfy `x (n + p) = x n`
    for all `n ≥ N`
    (concept `jis_term_4c219044135404e2d10fb16f`, statement `jis_a07921e69f2b6f8112afb1b1`). -/
def IsAperiodic (x : ℕ → Bool) : Prop :=
  ¬∃ p N : ℕ, 0 < p ∧ ∀ n : ℕ, N ≤ n → x (n + p) = x n

/-- An infinite binary word `x : ℕ → Bool` is Sturmian exactly when it is
    aperiodic and balanced (concept `jis_term_4c219044135404e2d10fb16f`,
    statement `jis_a07921e69f2b6f8112afb1b1`). -/
def IsSturmian (x : ℕ → Bool) : Prop :=
  IsAperiodic x ∧ IsBalanced x

end MetaMathlibExt
