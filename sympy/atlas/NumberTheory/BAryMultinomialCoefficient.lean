/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BAryMultinomialCoefficient.lean -/

import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Choose.Multinomial

namespace MetaMathlibExt

/-- Rank-`l` base-`b` digit of `n`, zero-padded beyond the most significant digit.

This is the `(k_i)_l` / `n_l` notation of source statement
`jis_2dd3152b04bd3c701907ca5c` (byte-identical duplicate
`jis_40ae94aec46faf8f37032d00`), concept `jis_term_48a88a0d7fe1b70bcdb0254d`,
semantic child `jis_sem_8f93866ba77d801d9ead13ca`
(`b-ary multinomial coefficient`).
Source: https://cs.uwaterloo.ca/journals/JIS/VOL19/Jiu/jiu3.tex
(`df0640a5d745b80e57565a61040414d4305680a9a5700ce376a717ffdc6f2571`),
span bytes/chars 16014..16622, lines 349..359,
raw TeX SHA-256 `ce098c5865cf6b3b380b6a679820635672ac58a52901ab8de41afd2c8a54d46b`. -/
def bAryDigit (b n l : ℕ) : ℕ := (Nat.digits b n).getD l 0

/-- List of rank-`l` base-`b` digits of each entry of `ks`.

Concept `jis_term_48a88a0d7fe1b70bcdb0254d`, semantic child
`jis_sem_8f93866ba77d801d9ead13ca`, statements `jis_2dd3152b04bd3c701907ca5c`
and `jis_40ae94aec46faf8f37032d00`. -/
def bAryLowerDigits (b : ℕ) (ks : List ℕ) (l : ℕ) : List ℕ :=
  ks.map (fun k => bAryDigit b k l)

/-- Ordinary multinomial factor with explicit top digit.

Mathlib `List.multinomial` takes the sum of `lowers` as its implicit top, so the
equality guard is required: the factor is zero unless the lower digits sum to
the top digit `top`. Concept `jis_term_48a88a0d7fe1b70bcdb0254d`, semantic
child `jis_sem_8f93866ba77d801d9ead13ca`, statements
`jis_2dd3152b04bd3c701907ca5c` and `jis_40ae94aec46faf8f37032d00`. -/
def ordinaryMultinomialFactor (top : ℕ) (lowers : List ℕ) : ℕ :=
  if lowers.sum = top then lowers.multinomial else 0

/-- Digitwise `b`-ary multinomial factor at rank `l`.

Top digit is the rank-`l` digit of `n`; lower digits are the rank-`l` digits of
`ks`. Concept `jis_term_48a88a0d7fe1b70bcdb0254d`, semantic child
`jis_sem_8f93866ba77d801d9ead13ca`, statements `jis_2dd3152b04bd3c701907ca5c`
and `jis_40ae94aec46faf8f37032d00`. -/
def bAryMultinomialFactor (b n : ℕ) (ks : List ℕ) (l : ℕ) : ℕ :=
  ordinaryMultinomialFactor (bAryDigit b n l) (bAryLowerDigits b ks l)

/-- Finite digit bound covering `n` and every entry of `ks`.

Takes the maximum of the digit-list lengths, so every nonzero digit lies below
the bound; beyond it all factors equal `1`, matching the source's sufficiently
large `N`. Concept `jis_term_48a88a0d7fe1b70bcdb0254d`, semantic child
`jis_sem_8f93866ba77d801d9ead13ca`, statements `jis_2dd3152b04bd3c701907ca5c`
and `jis_40ae94aec46faf8f37032d00`. -/
def bAryMultinomialBound (b n : ℕ) (ks : List ℕ) : ℕ :=
  max ((Nat.digits b n).length)
    (((ks.map (fun k => (Nat.digits b k).length)).max?).getD 0)

/-- The `b`-ary multinomial coefficient of `n` over lower indices `ks`.

Finite product of the digitwise factors below `bAryMultinomialBound`.
Requires `2 ≤ b` as data. Atomic coefficient definition from source statement
`jis_2dd3152b04bd3c701907ca5c` (byte-identical duplicate
`jis_40ae94aec46faf8f37032d00`), concept `jis_term_48a88a0d7fe1b70bcdb0254d`,
semantic child `jis_sem_8f93866ba77d801d9ead13ca`
(`b-ary multinomial coefficient`).
Source: https://cs.uwaterloo.ca/journals/JIS/VOL19/Jiu/jiu3.tex
(`df0640a5d745b80e57565a61040414d4305680a9a5700ce376a717ffdc6f2571`),
span bytes/chars 16014..16622, lines 349..359,
raw TeX SHA-256 `ce098c5865cf6b3b380b6a679820635672ac58a52901ab8de41afd2c8a54d46b`. -/
def bAryMultinomial (b n : ℕ) (ks : List ℕ) (hb : 2 ≤ b) : ℕ :=
  let _ : 2 ≤ b := hb
  (Finset.range (bAryMultinomialBound b n ks)).prod
    (fun l => bAryMultinomialFactor b n ks l)

end MetaMathlibExt
