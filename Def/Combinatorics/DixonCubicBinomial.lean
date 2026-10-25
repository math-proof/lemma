/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DixonCubicBinomial.lean -/

import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Rat.Star
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring


namespace MetaMathlibExt

open scoped BigOperators

noncomputable def xpoly (n k : ℚ) : ℚ :=
  (-58 - 392*n - 1042*n^2 - 1364*n^3 - 880*n^4 - 224*n^5)
  + k*(207/2 + 1113/2*n + 1107*n^2 + 966*n^3 + 312*n^4)
  + k^2*(-147/2 - 297*n - 396*n^2 - 174*n^3)
  + k^3*(24 + 66*n + 45*n^2)
  + k^4*(-3 - 9/2*n)

noncomputable def npoly (n k : ℚ) : ℚ :=
  (n+1)^2 * ((2*n+2)*(2*n+1))^3
  + 3*(3*n+1)*(3*n+2)*((2*n+2-k)^3*((2*n+1-k)^3))

noncomputable def Fq (n k : ℕ) : ℚ :=
  (-1 : ℚ)^k * ((Nat.choose (2*n) k : ℕ) : ℚ)^3

noncomputable def Gq (n k : ℕ) : ℚ :=
  if k = 0 ∨ 2*n+3 ≤ k then 0
  else (-1 : ℚ)^k * ((Nat.factorial (2*n) : ℕ) : ℚ)^3 * xpoly (n : ℚ) (k : ℚ)
    / ((((Nat.factorial (k-1) : ℕ) : ℚ)^3) * (((Nat.factorial (2*n+2-k) : ℕ) : ℚ)^3))

noncomputable def Sq (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (2*n+1), Fq n k

noncomputable def Dq (n : ℕ) : ℚ :=
  (-1 : ℚ)^n * (Nat.factorial (3*n) : ℚ) / ((Nat.factorial n : ℚ)^3)

end MetaMathlibExt
