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
import Def.NumberTheory.ContinuedFractions.LagrangePeriodic.Part4
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

/-- Every complete quotient past the head lies in the finite root set. -/
theorem cfXi_mem_triU (x : ℝ) (hx : Irrational x) (a b c : ℤ)
    (hquad : (a : ℝ) * x ^ 2 + (b : ℝ) * x + (c : ℝ) = 0)
    (noroot : ∀ q : ℚ, (a : ℝ) * (((q : ℚ)) : ℝ) ^ 2 + (b : ℝ) * (((q : ℚ)) : ℝ)
      + (c : ℝ) ≠ 0)
    (M K : ℕ)
    (hA : ∀ n, (triA a b c x n).natAbs ≤ M)
    (hB : ∀ n, (triB a b c x n).natAbs ≤ K)
    (hC : ∀ n, (triC a b c x n).natAbs ≤ M)
    (n : ℕ) :
    cfXi x (n + 1) ∈ triU M K := by
  have hbox := triple_mem_box a b c x M K hA hB hC n
  have hAne := triA_ne x hx a b c n noroot
  have h1 : (triA a b c x n, (triB a b c x n, triC a b c x n))
      ∈ (triBox M K).filter (fun t : ℤ × ℤ × ℤ => t.1 ≠ 0) :=
    Finset.mem_filter.mpr ⟨hbox, hAne⟩
  have h2 : (triPoly ((triA a b c x n : ℤ) : ℝ) ((triB a b c x n : ℤ) : ℝ)
      ((triC a b c x n : ℤ) : ℝ)).IsRoot (cfXi x (n + 1)) := by
    change (triPoly ((triA a b c x n : ℤ) : ℝ) ((triB a b c x n : ℤ) : ℝ)
      ((triC a b c x n : ℤ) : ℝ)).eval (cfXi x (n + 1)) = 0
    rw [triPoly_eval]
    exact tri_root x hx a b c n hquad
  exact Set.mem_biUnion (Finset.mem_coe.mpr h1) h2

end
end MetaMathlibExt
