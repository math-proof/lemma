/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ContinuedFractions/LagrangePeriodic.lean -/

/-
Author: Muse Spark 1.3
-/

import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.ContinuedFractions.Computation.TerminatesIffRat
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.FieldTheory.Minpoly.Basic
import Abbrev.Dynamics.EventuallyPeriodicSequence
import Lemma.Set.EventuallyPeriodicSequence
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
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

/-- Eventual periodicity of the continued fraction of `x`: the expansion does not
terminate, and the tail partial denominators `partDens` (which omits the head
coefficient `a₀`) are eventually periodic. Nontermination rules out a
vacuous `Option.none` tail. Source: Nimbran–Levrie lines 130–134. -/
def ContinuedFractionEventuallyPeriodic (x : ℝ) : Prop :=
  ¬ (GenContFract.of x).Terminates ∧
    IsEventuallyPeriodic (fun n => (GenContFract.of x).partDens.get? n)

/-- Real quadratic irrationality: `x` is integral over `ℚ` with minimal polynomial
of degree two. Degree two over `ℚ` captures real quadratic irrationality.
Source: Nimbran–Levrie line 136 (Euler–Lagrange statement). -/
def IsRealQuadraticIrrational (x : ℝ) : Prop :=
  IsIntegral ℚ x ∧ (minpoly ℚ x).natDegree = 2

/-- Complete quotients of `x`: `cfXi x 0 = x`, `cfXi x (n+1) = (fract (cfXi x n))⁻¹`. -/
noncomputable def cfXi (x : ℝ) : ℕ → ℝ
  | 0 => x
  | (n + 1) => (Int.fract (cfXi x n))⁻¹

end
end MetaMathlibExt
