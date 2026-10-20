import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Recurrences.FultonMorrisPisanoFixedPoint
open MetaMathlibExt


/--
[fulton_morris_pisano_fixed_point](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/FultonMorrisPisanoFixedPoint.lean)
-/
@[path]
private lemma fulton_morris_pisano_fixed_point_eq
  {m period : ℕ}
-- given
  (hm : 1 < m)
  (hperiod : 0 < period)
  (hreturn : Nat.ModEq m (Nat.fib period) 0 ∧ Nat.ModEq m (Nat.fib (period + 1)) 1)
  (hleast : ∀ t : ℕ, 0 < t → Nat.ModEq m (Nat.fib t) 0 → Nat.ModEq m (Nat.fib (t + 1)) 1 → period ≤ t) :
-- imply
  period = m ↔ ∃ lambda : ℕ, 0 < lambda ∧ m = 24 * 5 ^ (lambda - 1) := by
-- proof
  apply MetaMathlibExt.fulton_morris_pisano_fixed_point m period hm hperiod hreturn hleast


-- created on 2026-10-20
