/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/AignerMotzkinInequality.lean -/

import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Rat.Star
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring


namespace MetaMathlibExt

section

open scoped BigOperators

def Mot : ℕ → ℕ := fun r =>
  ∑ k ∈ Finset.range (r / 2 + 1),
    (Nat.choose (2 * k) k / (k + 1)) * Nat.choose r (2 * k)

noncomputable def t : ℕ → ℕ → ℚ := fun r k => (catalan k : ℚ) *
    ((Nat.choose r (2 * k) : ℕ) : ℚ)

noncomputable def H : ℕ → ℕ → ℚ
  | _, 0 => 0
  | n, (k + 1) => -4 * (((n : ℚ)) - 2 * ((k : ℚ))) * t n k

noncomputable def rat (n : ℕ) : ℚ := (Mot (n + 1) : ℚ) / (Mot n : ℚ)

noncomputable def LB (n : ℕ) : ℚ := (6 * (n + 1) : ℚ) / (2 * n + 5)

noncomputable def UB (n : ℕ) : ℚ := (3 * (2 * n + 3) : ℚ) / (2 * (n + 3))

end
end MetaMathlibExt
