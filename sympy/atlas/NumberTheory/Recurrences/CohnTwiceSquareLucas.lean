/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/CohnTwiceSquareLucas.lean -/

import sympy.atlas.NumberTheory.LucasSequence
import Lemma.Nat.LucasSequence
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace MetaMathlibExt

section
/-! # Square and twice-square Fibonacci and Lucas numbers

Source: Refik Keskin and Zafer Yosma, "On Fibonacci and Lucas Numbers of the
Form cx^2", Journal of Integer Sequences 14 (2011), Theorem 2.1, source
lines 129–132,
https://cs.uwaterloo.ca/journals/JIS/VOL14/Keskin/keskin3.tex
complete-source SHA-256
`f0f1dc8d3be32d14f8ad1f44e3c0fcf8c4081345df25ae0e814055b033901ea7`;
raw source-lines 129–132 SHA-256
`c8faa3153ac602a1bfc8d7488b4a14b64315ca1c39ad4ddf97245e574cb203dc`.

The source states: if `Fₙ = x²` then `n = 1, 2, 12`; if `Fₙ = 2x²` then
`n = 3, 6`; if `Lₙ = x²` then `n = 1, 3`; and if `Lₙ = 2x²` then `n = 6`.
The paper attributes the square-Fibonacci classification to J. H. E. Cohn,
"Square Fibonacci numbers, etc.", Fibonacci Quarterly 2.2 (1964), 109–113,
and the Lucas/twice-square classifications to Cohn's related work, including
"Lucas and Fibonacci numbers and some Diophantine equations", Proc. Glasgow
Math. Assoc. 7 (1965), 24–28.

The surrounding paper defines the Fibonacci and Lucas sequences at indices
`0` and `1` and discusses integer indices, but the displayed lists omit the
zero-index exceptions `F₀ = 0` and `L₀ = 2`. Each declaration below therefore
takes `(hn : 0 < n)` to formalize the intended positive-natural-index form.

`Nat.fib` is the Fibonacci sequence and `MetaMathlibExt.lucasNumber` is the
repository's canonical Lucas-number sequence; no parallel `Fₙ₋₁ + Fₙ₊₁`
encoding is used. -/

private def lz (n : ℕ) : ℤ := (lucasNumber n : ℤ)
end
end MetaMathlibExt
