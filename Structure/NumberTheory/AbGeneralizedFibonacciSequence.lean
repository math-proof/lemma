/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/AbGeneralizedFibonacciSequence.lean -/

import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.PowerSeries.Basic
/-!
# Kalman–Mena (a, b)-generalized Fibonacci sequence

Formalizes concept `jis_sem_34b8a222e3026d94d1de5306`
(source statement `jis_34b8a222e3026d94d1de5306`, Perminova, JIS VOL28):
for real parameters `a` and `b`, the sequence with `F 0 = 0`, `F 1 = 1`,
recurrence `F (n + 2) = a * F (n + 1) + b * F n`, and ordinary formal
generating series `x / (1 - a * x - b * x ^ 2)`.
-/


namespace MetaMathlibExt

/-- Kalman–Mena `(a, b)`-generalized Fibonacci sequence
(concept `jis_sem_34b8a222e3026d94d1de5306`;
source statement `jis_34b8a222e3026d94d1de5306`): real parameters `a`, `b`
together with a real-valued sequence satisfying `F 0 = 0`, `F 1 = 1`, the
recurrence `F (n + 2) = a * F (n + 1) + b * F n`, and the formal-power-series
identity for the ordinary generating series `x / (1 - a * x - b * x ^ 2)`. -/
structure AbGeneralizedFibonacciSequence where
  /-- Real parameter `a` (clause `domain`;
  concept `jis_sem_34b8a222e3026d94d1de5306`;
  source statement `jis_34b8a222e3026d94d1de5306`). -/
  a : ℝ
  /-- Real parameter `b` (clause `domain`;
  concept `jis_sem_34b8a222e3026d94d1de5306`;
  source statement `jis_34b8a222e3026d94d1de5306`). -/
  b : ℝ
  /-- The generalized Fibonacci sequence
  (concept `jis_sem_34b8a222e3026d94d1de5306`;
  source statement `jis_34b8a222e3026d94d1de5306`). -/
  F : ℕ → ℝ
  /-- Initial value `F 0 = 0` (clause `initial_zero`;
  concept `jis_sem_34b8a222e3026d94d1de5306`;
  source statement `jis_34b8a222e3026d94d1de5306`). -/
  initial_zero : F 0 = 0
  /-- Initial value `F 1 = 1` (clause `initial_one`;
  concept `jis_sem_34b8a222e3026d94d1de5306`;
  source statement `jis_34b8a222e3026d94d1de5306`). -/
  initial_one : F 1 = 1
  /-- Recurrence `F (n + 2) = a * F (n + 1) + b * F n` (clause `recurrence`;
  concept `jis_sem_34b8a222e3026d94d1de5306`;
  source statement `jis_34b8a222e3026d94d1de5306`). -/
  recurrence : ∀ n : ℕ, F (n + 2) = a * F (n + 1) + b * F n
  /-- Ordinary generating series identity
  `(1 - a * X - b * X ^ 2) * mk F = X`, i.e. `mk F = x / (1 - a * x - b * x ^ 2)`
  (clause `generating_function`;
  concept `jis_sem_34b8a222e3026d94d1de5306`;
  source statement `jis_34b8a222e3026d94d1de5306`). -/
  gen_eq :
    (1 - PowerSeries.C a * PowerSeries.X - PowerSeries.C b * PowerSeries.X ^ 2) *
      PowerSeries.mk F = PowerSeries.X

end MetaMathlibExt
