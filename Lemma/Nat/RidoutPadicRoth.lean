import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RidoutPadicRoth
open scoped BigOperators
open MetaMathlibExt


/--
[ridout_padic_roth](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RidoutPadicRoth.lean)
-/
@[path]
private lemma ridout_padic_roth_eq
  {ξ ε : ℝ}
  {S : Finset Nat.Primes}
-- given
  (hξ : IsAlgebraic ℚ ξ)
  (hξi : Irrational ξ)
  (hε : 0 < ε) :
-- imply
  Set.Finite {r : ℚ |
    ((∏ ℓ ∈ S, padicNorm ℓ.1 (r.num : ℚ) * padicNorm ℓ.1 (r.den : ℚ) : ℚ) : ℝ) *
    |ξ - (r : ℝ)| <
    (((max r.num.natAbs r.den : ℕ) : ℝ) ^ (2 + ε))⁻¹} := by
-- proof
  apply MetaMathlibExt.ridout_padic_roth ξ hξ hξi ε hε S


-- created on 2026-10-20
