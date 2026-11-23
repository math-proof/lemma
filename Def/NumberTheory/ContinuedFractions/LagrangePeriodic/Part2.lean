/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ContinuedFractions/LagrangePeriodic.lean -/

/-
Author: Muse Spark 1.3
-/

module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.ContinuedFractions.Computation.TerminatesIffRat
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.FieldTheory.Minpoly.Basic
public import Abbrev.Dynamics.EventuallyPeriodicSequence
public import Theorem.Set.EventuallyPeriodicSequence
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Data.Int.Star
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import Theorem.NumberTheory.ContinuedFractions.LagrangePeriodic

@[expose] public section

/-!
# Euler–Lagrange theorem on eventually periodic continued fractions

This file proves the Lagrange direction of the Euler–Lagrange characterization
of eventually periodic continued fractions: a real quadratic irrational has an
eventually periodic continued fraction
(`continuedFractionEventuallyPeriodic_of_isRealQuadraticIrrational`).

The canonical biconditional
(`continuedFractionEventuallyPeriodic_iff_isRealQuadraticIrrational`) and the
Euler direction
(`isRealQuadraticIrrational_of_continuedFractionEventuallyPeriodic`) are proved
in `MathlibExt.NumberTheory.ContinuedFractions.EulerPeriodic`.

## Sources

* Amrik Singh Nimbran and Paul Levrie, "Patterns in Continued Fractions of
  Square Roots," Journal of Integer Sequences 26 (2023),
  <https://cs.uwaterloo.ca/journals/JIS/VOL26/Nimbran/nimbran14.tex>.
* The eventual-periodicity definition is lines 130–134; exact newline-terminated
  raw span SHA-256:
  `6d3b24948521d4d3fa03d6e17261c9442aa6cdf875126db573c9575a66623a7e`.
* The Euler–Lagrange statement is line 136; exact newline-terminated raw span
  SHA-256:
  `5be80578f3e620afa4d20050b29627a4c251e6ff852720806a9a42a0ff884b42`.
* Complete source file SHA-256:
  `08f38fd112c2dedb3802fe71799b670f6d2dbf5f49a89afdc0828156b8f56180`.
* Archive: `lagrange_periodic_cf_release_v2_D119163759`.
-/


namespace MetaMathlibExt

section

/-- Numerator convergents: `P 0 = 1`, `P 1 = ⌊x⌋`, `P (n+2) = ⌊ξ (n+1)⌋ P (n+1) + P n`. -/
noncomputable def cfP (x : ℝ) : ℕ → ℤ
  | 0 => 1
  | 1 => ⌊x⌋
  | (n + 2) => ⌊cfXi x (n + 1)⌋ * cfP x (n + 1) + cfP x n

/-- Denominator convergents: `Q 0 = 0`, `Q 1 = 1`, `Q (n+2) = ⌊ξ (n+1)⌋ Q (n+1) + Q n`. -/
noncomputable def cfQ (x : ℝ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | (n + 2) => ⌊cfXi x (n + 1)⌋ * cfQ x (n + 1) + cfQ x n

end
end MetaMathlibExt
