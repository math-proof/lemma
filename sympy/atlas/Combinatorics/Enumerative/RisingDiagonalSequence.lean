/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/RisingDiagonalSequence.lean -/

import Mathlib.Data.Real.Basic

/-!
# Rising diagonals of binary binomial interpolated triangles

Source: L. Németh, *On the binomial interpolated triangles*, Journal of Integer
Sequences 20 (2017), Article 17.7.2,
[`nemeth2.tex`](https://cs.uwaterloo.ca/journals/JIS/VOL20/Nemeth/nemeth2.tex).

The Case 1 triangle `BT(a₀,a₁,α,β;α,β)` is fixed by the column-zero recurrence
and the interior recurrence below. Its corollary (source lines 760–865) states
that every rising diagonal of this triangle is constant.
-/

namespace MetaMathlibExt

/-- The source's binary binomial interpolated triangle `BT(a₀,a₁,α,β;α,β)`. -/
def IsBinaryBinomialInterpolatedTriangle
    (a : ℕ → ℕ → ℝ) (a₀ a₁ α β : ℝ) : Prop :=
  α * β ≠ 0 ∧ |a₀| + |a₁| ≠ 0 ∧
    a 0 0 = a₀ ∧ a 1 0 = a₁ ∧
    (∀ n, 2 ≤ n → a n 0 = α * a (n - 1) 0 + β * a (n - 2) 0) ∧
    ∀ n k, 1 ≤ k → k ≤ n →
      a n k = α * a n (k - 1) + β * a (n - 1) (k - 1)

/-- The rising diagonal at level `n`, namely `a (n-k) k` for `0 ≤ k ≤ ⌊n/2⌋`. -/
def risingDiagonal (a : ℕ → ℕ → ℝ) (n : ℕ) : Fin (n / 2 + 1) → ℝ :=
  fun k => a (n - k) k
end MetaMathlibExt
