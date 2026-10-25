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
import Def.NumberTheory.ContinuedFractions.LagrangePeriodic.Part3
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

/-- Each complete quotient is a root of its auxiliary integer quadratic. -/
theorem tri_root (x : ℝ) (hx : Irrational x) (a b c : ℤ) (n : ℕ)
    (hquad : (a : ℝ) * x ^ 2 + (b : ℝ) * x + (c : ℝ) = 0) :
    ((triA a b c x n : ℤ) : ℝ) * (cfXi x (n + 1)) ^ 2
      + ((triB a b c x n : ℤ) : ℝ) * (cfXi x (n + 1))
      + ((triC a b c x n : ℤ) : ℝ) = 0 := by
  obtain ⟨hQ0, hQ1⟩ := cfQ_nonneg_pos x hx n
  have hQ1R : (1 : ℝ) ≤ (cfQ x (n + 1) : ℝ) := by exact_mod_cast hQ1
  have hQ0R : (0 : ℝ) ≤ (cfQ x n : ℝ) := by exact_mod_cast hQ0
  have hs : (1 : ℝ) < cfXi x (n + 1) := one_lt_cfXi_succ x hx n
  have hden_ne : (cfQ x (n + 1) : ℝ) * cfXi x (n + 1) + (cfQ x n : ℝ) ≠ 0 := by
    have hpos : (0 : ℝ) < (cfQ x (n + 1) : ℝ) * cfXi x (n + 1) :=
      mul_pos (by linarith) (by linarith)
    have hlt : (0 : ℝ) < (cfQ x (n + 1) : ℝ) * cfXi x (n + 1) + (cfQ x n : ℝ) := by
      linarith
    exact ne_of_gt hlt
  have hmob := cfMobius x hx n
  have h2 : x * ((cfQ x (n + 1) : ℝ) * cfXi x (n + 1) + (cfQ x n : ℝ))
      = (cfP x (n + 1) : ℝ) * cfXi x (n + 1) + (cfP x n : ℝ) := by
    have h3 : ((cfP x (n + 1) : ℝ) * cfXi x (n + 1) + (cfP x n : ℝ))
          / ((cfQ x (n + 1) : ℝ) * cfXi x (n + 1) + (cfQ x n : ℝ))
          * ((cfQ x (n + 1) : ℝ) * cfXi x (n + 1) + (cfQ x n : ℝ))
        = (cfP x (n + 1) : ℝ) * cfXi x (n + 1) + (cfP x n : ℝ) :=
      div_mul_cancel₀ _ hden_ne
    rw [← hmob] at h3
    exact h3
  have e1 : ((triA a b c x n : ℤ) : ℝ) * (cfXi x (n + 1)) ^ 2
        + ((triB a b c x n : ℤ) : ℝ) * (cfXi x (n + 1))
        + ((triC a b c x n : ℤ) : ℝ)
      = (a : ℝ) * ((cfP x (n + 1) : ℝ) * cfXi x (n + 1) + (cfP x n : ℝ)) ^ 2
        + (b : ℝ) * ((cfP x (n + 1) : ℝ) * cfXi x (n + 1) + (cfP x n : ℝ))
          * ((cfQ x (n + 1) : ℝ) * cfXi x (n + 1) + (cfQ x n : ℝ))
        + (c : ℝ) * ((cfQ x (n + 1) : ℝ) * cfXi x (n + 1) + (cfQ x n : ℝ)) ^ 2 := by
    simp only [triA, triB, triC]
    push_cast
    ring
  have e2 : (a : ℝ) * ((cfP x (n + 1) : ℝ) * cfXi x (n + 1) + (cfP x n : ℝ)) ^ 2
        + (b : ℝ) * ((cfP x (n + 1) : ℝ) * cfXi x (n + 1) + (cfP x n : ℝ))
          * ((cfQ x (n + 1) : ℝ) * cfXi x (n + 1) + (cfQ x n : ℝ))
        + (c : ℝ) * ((cfQ x (n + 1) : ℝ) * cfXi x (n + 1) + (cfQ x n : ℝ)) ^ 2
      = ((cfQ x (n + 1) : ℝ) * cfXi x (n + 1) + (cfQ x n : ℝ)) ^ 2
        * ((a : ℝ) * x ^ 2 + (b : ℝ) * x + (c : ℝ)) := by
    rw [← h2]
    ring
  rw [e1, e2, hquad, mul_zero]

/-- Uniform real bound on the leading coefficients. -/
theorem triA_real_le (x : ℝ) (hx : Irrational x) (a b c : ℤ)
    (hquad : (a : ℝ) * x ^ 2 + (b : ℝ) * x + (c : ℝ) = 0) (n : ℕ) :
    |((triA a b c x n : ℤ) : ℝ)|
      ≤ |(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)| := by
  obtain ⟨hQ0, hQ1⟩ := cfQ_nonneg_pos x hx n
  have hQ1R : (1 : ℝ) ≤ ((cfQ x (n + 1) : ℤ) : ℝ) := by exact_mod_cast hQ1
  have hQnn : (0 : ℝ) ≤ ((cfQ x (n + 1) : ℤ) : ℝ) := by linarith
  set Q' : ℝ := ((cfQ x (n + 1) : ℤ) : ℝ) with hQ'def
  set P' : ℝ := ((cfP x (n + 1) : ℤ) : ℝ) with hP'def
  set F : ℝ := Q' * x - P' with hFdef
  have hFle : |Q' * x - P'| ≤ 1 / Q' := by
    rw [hQ'def, hP'def]
    exact (cfApprox x hx n).2
  have hFleF : |F| ≤ 1 / Q' := by rw [hFdef]; exact hFle
  have hQne : Q' ≠ 0 := ne_of_gt (by linarith)
  have hFQ : |F| * Q' ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hFleF hQnn
    rwa [one_div_mul_cancel hQne] at h
  have hF1 : |F| ≤ 1 := by
    calc |F| = |F| * 1 := (mul_one _).symm
      _ ≤ |F| * Q' := mul_le_mul_of_nonneg_left hQ1R (abs_nonneg _)
      _ ≤ 1 := hFQ
  have hF2 : F ^ 2 ≤ 1 := by
    have h := mul_le_mul hF1 hF1 (abs_nonneg F) zero_le_one
    rw [one_mul, ← pow_two, sq_abs] at h
    exact h
  have hFproof : F = ((cfQ x (n + 1) : ℤ) : ℝ) * x - ((cfP x (n + 1) : ℤ) : ℝ) := by
    rw [hFdef, hQ'def, hP'def]
  have hform := triA_eq_form x a b c n hquad F hFproof
  rw [hform]
  calc |((a : ℝ)) * F ^ 2 - F * Q' * (2 * (a : ℝ) * x + (b : ℝ))|
      ≤ |((a : ℝ)) * F ^ 2| + |F * Q' * (2 * (a : ℝ) * x + (b : ℝ))| := by
        have h := abs_add_le ((a : ℝ) * F ^ 2)
          (-(F * Q' * (2 * (a : ℝ) * x + (b : ℝ))))
        rwa [← sub_eq_add_neg, abs_neg] at h
    _ ≤ |(a : ℝ)| * 1 + 1 * |2 * (a : ℝ) * x + (b : ℝ)| := by
        refine add_le_add ?_ ?_
        · simp only [abs_mul, abs_of_nonneg (sq_nonneg F)]
          exact mul_le_mul_of_nonneg_left hF2 (abs_nonneg _)
        · simp only [abs_mul, abs_of_nonneg hQnn]
          exact mul_le_mul_of_nonneg_right hFQ (abs_nonneg _)
    _ = |(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)| := by rw [mul_one, one_mul]

/-- The leading coefficients take finitely many values. -/
theorem triA_bound (x : ℝ) (hx : Irrational x) (a b c : ℤ)
    (hquad : (a : ℝ) * x ^ 2 + (b : ℝ) * x + (c : ℝ) = 0) :
    ∃ M : ℕ, ∀ n : ℕ, (triA a b c x n).natAbs ≤ M := by
  refine ⟨⌈|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|⌉₊, fun n => ?_⟩
  have hA := triA_real_le x hx a b c hquad n
  have hM : |(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|
      ≤ ((⌈|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|⌉₊ : ℕ) : ℝ) :=
    Nat.le_ceil _
  have hle : |((triA a b c x n : ℤ) : ℝ)|
      ≤ ((⌈|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|⌉₊ : ℕ) : ℝ) :=
    le_trans hA hM
  have g1 : triA a b c x n
      ≤ ((⌈|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|⌉₊ : ℕ) : ℤ) := by
    exact_mod_cast (abs_le.mp hle).2
  have g2 : -((⌈|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|⌉₊ : ℕ) : ℤ)
      ≤ triA a b c x n := by
    exact_mod_cast (abs_le.mp hle).1
  omega

/-- Uniform real bound on the constant coefficients. -/
theorem triC_real_le (x : ℝ) (hx : Irrational x) (a b c : ℤ)
    (hquad : (a : ℝ) * x ^ 2 + (b : ℝ) * x + (c : ℝ) = 0) (n : ℕ) :
    |((triC a b c x n : ℤ) : ℝ)|
      ≤ |(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)| := by
  cases n with
  | zero =>
    have hC0 : triC a b c x 0 = a := by simp [triC, cfP_zero, cfQ_zero]
    rw [hC0]
    exact le_add_of_nonneg_right (abs_nonneg _)
  | succ n =>
    rw [triC_succ]
    exact triA_real_le x hx a b c hquad n

/-- The constant coefficients take finitely many values. -/
theorem triC_bound (x : ℝ) (hx : Irrational x) (a b c : ℤ)
    (hquad : (a : ℝ) * x ^ 2 + (b : ℝ) * x + (c : ℝ) = 0) :
    ∃ M : ℕ, ∀ n : ℕ, (triC a b c x n).natAbs ≤ M := by
  refine ⟨⌈|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|⌉₊, fun n => ?_⟩
  have hC := triC_real_le x hx a b c hquad n
  have hM : |(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|
      ≤ ((⌈|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|⌉₊ : ℕ) : ℝ) :=
    Nat.le_ceil _
  have hle : |((triC a b c x n : ℤ) : ℝ)|
      ≤ ((⌈|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|⌉₊ : ℕ) : ℝ) :=
    le_trans hC hM
  have g1 : triC a b c x n
      ≤ ((⌈|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|⌉₊ : ℕ) : ℤ) := by
    exact_mod_cast (abs_le.mp hle).2
  have g2 : -((⌈|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|⌉₊ : ℕ) : ℤ)
      ≤ triC a b c x n := by
    exact_mod_cast (abs_le.mp hle).1
  omega

/-- The middle coefficients take finitely many values. -/
theorem triB_bound (x : ℝ) (hx : Irrational x) (a b c : ℤ)
    (hquad : (a : ℝ) * x ^ 2 + (b : ℝ) * x + (c : ℝ) = 0) :
    ∃ K : ℕ, ∀ n : ℕ, (triB a b c x n).natAbs ≤ K := by
  have hA : ∀ n, |((triA a b c x n : ℤ) : ℝ)|
      ≤ |(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)| :=
    fun n => triA_real_le x hx a b c hquad n
  have hC : ∀ n, |((triC a b c x n : ℤ) : ℝ)|
      ≤ |(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)| :=
    fun n => triC_real_le x hx a b c hquad n
  have hRnn : (0 : ℝ) ≤ |(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)| :=
    add_nonneg (abs_nonneg _) (abs_nonneg _)
  refine ⟨⌈|((b ^ 2 - 4 * a * c : ℤ) : ℝ)|
      + 4 * ((|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)
        * (|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)) + 1⌉₊, fun n => ?_⟩
  have hBn := triB_sq x a b c n
  have hAn := hA n
  have hCn := hC n
  have hAC : ((triA a b c x n : ℤ) : ℝ) * ((triC a b c x n : ℤ) : ℝ)
      ≤ (|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)
        * (|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|) :=
    calc ((triA a b c x n : ℤ) : ℝ) * ((triC a b c x n : ℤ) : ℝ)
        ≤ |((triA a b c x n : ℤ) : ℝ) * ((triC a b c x n : ℤ) : ℝ)| :=
          le_abs_self _
      _ = |((triA a b c x n : ℤ) : ℝ)| * |((triC a b c x n : ℤ) : ℝ)| :=
          abs_mul _ _
      _ ≤ (|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)
          * (|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|) :=
          mul_le_mul hAn hCn (abs_nonneg _) hRnn
  have hB2 : ((triB a b c x n : ℤ) : ℝ) ^ 2
      ≤ |((b ^ 2 - 4 * a * c : ℤ) : ℝ)|
        + 4 * ((|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)
          * (|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)) := by
    have hDle : ((b ^ 2 - 4 * a * c : ℤ) : ℝ)
        ≤ |((b ^ 2 - 4 * a * c : ℤ) : ℝ)| := le_abs_self _
    rw [hBn]
    linear_combination hDle + 4 * hAC
  have hBb : |((triB a b c x n : ℤ) : ℝ)|
      ≤ |((b ^ 2 - 4 * a * c : ℤ) : ℝ)|
        + 4 * ((|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)
          * (|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)) + 1 := by
    by_cases h1 : |((triB a b c x n : ℤ) : ℝ)| ≤ 1
    · calc |((triB a b c x n : ℤ) : ℝ)| ≤ 1 := h1
        _ ≤ |((b ^ 2 - 4 * a * c : ℤ) : ℝ)|
            + 4 * ((|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)
              * (|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)) + 1 := by
            have h1' : (0 : ℝ) ≤ |((b ^ 2 - 4 * a * c : ℤ) : ℝ)| := abs_nonneg _
            have h2' : (0 : ℝ) ≤ (|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)
                * (|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|) :=
              mul_nonneg hRnn hRnn
            linarith
    · push Not at h1
      calc |((triB a b c x n : ℤ) : ℝ)| ≤ ((triB a b c x n : ℤ) : ℝ) ^ 2 := by
            calc |((triB a b c x n : ℤ) : ℝ)|
                = |((triB a b c x n : ℤ) : ℝ)| * 1 := (mul_one _).symm
              _ ≤ |((triB a b c x n : ℤ) : ℝ)|
                  * |((triB a b c x n : ℤ) : ℝ)| :=
                  mul_le_mul_of_nonneg_left h1.le (abs_nonneg _)
              _ = ((triB a b c x n : ℤ) : ℝ) ^ 2 := by rw [← pow_two, sq_abs]
        _ ≤ |((b ^ 2 - 4 * a * c : ℤ) : ℝ)|
            + 4 * ((|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)
              * (|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)) := hB2
        _ ≤ |((b ^ 2 - 4 * a * c : ℤ) : ℝ)|
            + 4 * ((|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)
              * (|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)) + 1 :=
            le_add_of_nonneg_right zero_le_one
  have hK : |((b ^ 2 - 4 * a * c : ℤ) : ℝ)|
        + 4 * ((|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)
          * (|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)) + 1
      ≤ ((⌈|((b ^ 2 - 4 * a * c : ℤ) : ℝ)|
        + 4 * ((|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)
          * (|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)) + 1⌉₊ : ℕ) : ℝ) :=
    Nat.le_ceil _
  have hle : |((triB a b c x n : ℤ) : ℝ)|
      ≤ ((⌈|((b ^ 2 - 4 * a * c : ℤ) : ℝ)|
        + 4 * ((|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)
          * (|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)) + 1⌉₊ : ℕ) : ℝ) :=
    le_trans hBb hK
  have g1 : triB a b c x n
      ≤ ((⌈|((b ^ 2 - 4 * a * c : ℤ) : ℝ)|
        + 4 * ((|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)
          * (|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)) + 1⌉₊ : ℕ) : ℤ) := by
    exact_mod_cast (abs_le.mp hle).2
  have g2 : -((⌈|((b ^ 2 - 4 * a * c : ℤ) : ℝ)|
        + 4 * ((|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)
          * (|(a : ℝ)| + |2 * (a : ℝ) * x + (b : ℝ)|)) + 1⌉₊ : ℕ) : ℤ)
      ≤ triB a b c x n := by
    exact_mod_cast (abs_le.mp hle).1
  omega

/-- Each complete quotient determines the next via the floor. -/
theorem cfXi_step (x : ℝ) (k : ℕ) :
    cfXi x (k + 2) = 1 / (cfXi x (k + 1) - ⌊cfXi x (k + 1)⌋) := by
  have hfr : cfXi x (k + 1) - ⌊cfXi x (k + 1)⌋
      = Int.fract (cfXi x (k + 1)) := by
    have h := Int.floor_add_fract (cfXi x (k + 1))
    linarith
  rw [hfr, cfXi_succ]
  exact (one_div _).symm

/-- Complete quotients commute with shifting past one step. -/
theorem cfXi_shift (v : ℝ) (k : ℕ) :
    cfXi ((Int.fract v)⁻¹) k = cfXi v (k + 1) := by
  induction k with
  | zero => rw [cfXi_zero, cfXi_succ, cfXi_zero]
  | succ k ih => rw [cfXi_succ, cfXi_succ, ih]

/-- The `n`-th partial denominator is the head coefficient of `ξₙ`. -/
theorem partDens_eq_head (x : ℝ) (n : ℕ) :
    (GenContFract.of x).partDens.get? n
      = (GenContFract.of (cfXi x n)).partDens.get? 0 := by
  revert x
  induction n with
  | zero => intro x; rw [cfXi_zero]
  | succ n ih =>
    intro v
    have e : cfXi ((Int.fract v)⁻¹) n = (Int.fract (cfXi v n))⁻¹ := by
      rw [cfXi_shift, cfXi_succ]
    rw [partDens_shift v n, cfXi_succ, ← e]
    exact ih ((Int.fract v)⁻¹)

end
end MetaMathlibExt
