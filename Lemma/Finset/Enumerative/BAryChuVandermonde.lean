import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.BAryChuVandermonde
open MetaMathlibExt


/--
[bAryBinomialCoefficient_chu_vandermonde](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BAryChuVandermonde.lean)
-/
@[path]
private lemma bAryBinomialCoefficient_chu_vandermonde_eq
  {b m n r : ℕ}
-- given
  (hb : 2 ≤ b)
  (hcarry : ∀ l, (m / b ^ l) % b + (n / b ^ l) % b < b) :
-- imply
  bAryBinomialCoefficient b (m + n) r hb =
    ∑ k ∈ Finset.range (r + 1),
    bAryBinomialCoefficient b m k hb * bAryBinomialCoefficient b n (r - k) hb := by
-- proof
  apply MetaMathlibExt.bAryBinomialCoefficient_chu_vandermonde b m n r hb hcarry

/--
[bary_chu_vandermonde](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BAryChuVandermonde.lean)
-/
@[path]
private lemma bary_chu_vandermonde_eq
  {b m n r : ℕ}
-- given
  (hb : 2 ≤ b)
  (hcarry : ∀ l ∈ Finset.range (m + n + 1), (m / b ^ l) % b + (n / b ^ l) % b < b) :
-- imply
  (let C : ℕ → ℕ → ℕ := by
-- proof
  apply MetaMathlibExt.bary_chu_vandermonde b m n r hb hcarry


-- created on 2026-10-20
