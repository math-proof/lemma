/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/AignerMotzkinInequality.lean -/

module

public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Data.Nat.Cast.Field
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Data.Rat.Star
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

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
