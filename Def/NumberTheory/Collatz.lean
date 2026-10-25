/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Collatz.lean -/

import Mathlib.Data.Nat.Notation
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.Lattice.Nat
/-!
# Collatz iteration

Shared definitions for the Collatz map, its iterates, and the stopping time.
-/


namespace Nat

/-- One step of the Collatz map. -/
def collatzStep (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

/-- The result of applying `collatzStep` exactly `k` times to `n`. -/
def collatzIterate : ℕ → ℕ → ℕ
  | 0, n => n
  | k + 1, n => collatzStep (collatzIterate k n)

open Classical in
/-- The least number of Collatz steps needed to reach `1`, or `none` for zero
and for values not known to reach `1`. -/
noncomputable def collatzStoppingTime (n : ℕ) : Option ℕ :=
  if n = 0 then none
  else if ∃ k : ℕ, collatzIterate k n = 1 then
    some (sInf {k : ℕ | collatzIterate k n = 1})
  else
    none

end Nat
